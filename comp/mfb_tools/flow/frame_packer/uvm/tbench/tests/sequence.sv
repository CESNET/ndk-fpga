// sequence.sv: Virtual sequence
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): David Beneš <xbenes52@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class virt_sequence#(
    int unsigned MFB_REGIONS,
    int unsigned MFB_REGION_SIZE,
    int unsigned MFB_BLOCK_SIZE,
    int unsigned MFB_ITEM_WIDTH,
    int unsigned RX_CHANNELS,
    int unsigned PKT_MTU
) extends uvm_sequence;
    `uvm_object_param_utils(
        test::virt_sequence #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, RX_CHANNELS, PKT_MTU))
    `uvm_declare_p_sequencer(uvm_framepacker::virt_sequencer#(MFB_ITEM_WIDTH, PKT_MTU, RX_CHANNELS, HDR_META_WIDTH))

    function new (string name = "virt_sequence");
        super.new(name);
    endfunction

    //RX
    uvm_reset::sequence_start                             m_reset;
    uvm_logic_vector_array::sequence_lib#(MFB_ITEM_WIDTH) m_mfb_data_seq;

    //TX DST_RDY handle
    uvm_meta::sequence_lib #(PKT_MTU, RX_CHANNELS, HDR_META_WIDTH)                 m_info_seq;

    protected int unsigned frame_size_min;
    protected int unsigned frame_size_max;

    // Number of MFB data sequences - the traffic is paused between them to let the timeouts expire
    rand int unsigned mfb_seq_count;
    constraint c_mfb_seq_count {mfb_seq_count inside {[SEQ_MIN : SEQ_MAX]};}

    virtual function void init(int unsigned frame_size_min, int unsigned frame_size_max);
        m_reset         = uvm_reset::sequence_start::type_id::create("m_reset");
        m_info_seq      = uvm_meta::sequence_lib #(PKT_MTU, RX_CHANNELS, HDR_META_WIDTH)::type_id::create("m_info_seq");

        this.frame_size_min = frame_size_min;
        this.frame_size_max = frame_size_max;

        m_info_seq.init_sequence();
        m_info_seq.min_random_count = 200000;
        m_info_seq.max_random_count = 500000;
    endfunction

    virtual function void mfb_data_seq_create();
        m_mfb_data_seq  = uvm_logic_vector_array::sequence_lib#(MFB_ITEM_WIDTH)::type_id::create("m_mfb_data_seq");
        m_mfb_data_seq.init_sequence();
        m_mfb_data_seq.add_sequence(sequence_small_big#(MFB_ITEM_WIDTH)::get_type());
        m_mfb_data_seq.cfg = new();
        m_mfb_data_seq.cfg.array_size_set(frame_size_min, frame_size_max);
        m_mfb_data_seq.min_random_count = 1;
        m_mfb_data_seq.max_random_count = 1;
    endfunction

    virtual task run_reset();

        m_reset.randomize();
        m_reset.start(p_sequencer.m_reset);

    endtask

    virtual task run_mfb_data();
        for (int unsigned it = 0; it < mfb_seq_count; it++) begin
            mfb_data_seq_create();
            assert(m_mfb_data_seq.randomize());
            m_mfb_data_seq.start(p_sequencer.m_mfb_data_sqr);

            // Idle on RX - timeouts expire in the middle of the traffic, not only at the end of the test
            if (it + 1 < mfb_seq_count && $urandom_range(99) < RX_GAP_PROBABILITY) begin
                #($urandom_range(TIMEOUT_CLK_NO/2, 2*TIMEOUT_CLK_NO)*CLK_PERIOD);
            end
        end
    endtask

    // Only one directed packet is generated at a time - the data and the channel have to be paired
    protected semaphore directed_lock;

    // Sends one packet with size in the given range to the given channel
    virtual task send_one(int unsigned channel, int unsigned size_min, int unsigned size_max);
        sequence_one_packet #(MFB_ITEM_WIDTH)                           data_seq;
        sequence_one_channel #(PKT_MTU, RX_CHANNELS, HDR_META_WIDTH)    info_seq;

        data_seq          = sequence_one_packet #(MFB_ITEM_WIDTH)::type_id::create("data_seq");
        data_seq.size_min = size_min;
        data_seq.size_max = size_max;
        info_seq          = sequence_one_channel #(PKT_MTU, RX_CHANNELS, HDR_META_WIDTH)::type_id::create("info_seq");
        info_seq.channel  = channel;

        fork
            data_seq.start(p_sequencer.m_mfb_data_sqr);
            info_seq.start(p_sequencer.m_info);
        join
    endtask

    virtual task send_packet(int unsigned channel, int unsigned size_min, int unsigned size_max);
        directed_lock.get();
        send_one(channel, size_min, size_max);
        directed_lock.put();
    endtask

    // Sends a packet to another channel directly followed by a packet to the given channel - the second packet starts
    // in the middle of the MFB word and continues in the next word
    virtual task send_packet_pair(int unsigned channel_first, int unsigned channel, int unsigned size_min,
                                  int unsigned size_max);
        directed_lock.get();
        send_one(channel_first, size_min, size_max);
        send_one(channel, size_min, size_max);
        directed_lock.put();
    endtask

    // Directed timeout scenario of one channel. The first repetitions send a minimal packet and then a packet
    // incomplete in the MFB word just when the timeout counter expires (a race of the new data and the timeout, index
    // selects the offset). In the last repetition, a small packet comes after the timeout and no more data comes to
    // the channel - it has to be sent by a repeated timeout.
    virtual task run_timeout_channel(int unsigned channel, int unsigned channel_other, int unsigned index,
                                     int unsigned channel_count);
        int unsigned small_max = (frame_size_min + 64 < frame_size_max) ? frame_size_min + 64  : frame_size_max;
        int unsigned mid_min   = (frame_size_min + 64 < frame_size_max) ? frame_size_min + 64  : frame_size_max;
        int unsigned mid_max   = (frame_size_min + 128 < frame_size_max) ? frame_size_min + 128 : frame_size_max;

        // The channels do not send at the same time
        #(index*40*CLK_PERIOD);

        for (int unsigned it = 0; it < TIMEOUT_DIRECTED_REPEAT; it++) begin
            if (it + 1 < TIMEOUT_DIRECTED_REPEAT) begin
                send_packet(channel, frame_size_min, frame_size_min);
                // The offsets -12 .. 11 around the timeout cover the latency of the DUT input
                #((TIMEOUT_CLK_NO - 12 + (index + it*channel_count) % 24)*CLK_PERIOD);
                send_packet_pair(channel_other, channel, mid_min, mid_max);
                // Let all timeouts of the channels expire
                #(2*TIMEOUT_CLK_NO*CLK_PERIOD);
            end else begin
                send_packet(channel, frame_size_min, small_max);
                #($urandom_range(TIMEOUT_CLK_NO + 32, 2*TIMEOUT_CLK_NO)*CLK_PERIOD);
                send_packet(channel, frame_size_min, small_max);
            end
        end
    endtask

    // Runs the directed timeout scenario on several channels in parallel
    virtual task run_timeout_directed();
        int unsigned channels[RX_CHANNELS];
        int unsigned channel_count = (TIMEOUT_DIRECTED_CHANNELS < RX_CHANNELS) ? TIMEOUT_DIRECTED_CHANNELS
                                                                                : RX_CHANNELS;

        directed_lock = new(1);
        // The data of the random traffic is sent by the timeouts first
        #(2*TIMEOUT_CLK_NO*CLK_PERIOD);
        foreach (channels[it]) begin
            channels[it] = it;
        end
        channels.shuffle();

        // The outer fork isolates wait fork from the other processes of the sequence
        fork
            begin
                for (int unsigned it = 0; it < channel_count; it++) begin
                    fork
                        automatic int unsigned channel       = channels[it];
                        // The previous channel of the scenario is used for the first packet of the pair
                        automatic int unsigned channel_other = channels[(it + channel_count - 1) % channel_count];
                        automatic int unsigned index         = it;
                        run_timeout_channel(channel, channel_other, index, channel_count);
                    join_none
                end
                wait fork;
            end
        join
    endtask

    task body();

        // init();

        fork
            run_reset();
        join_none

        #(200ns)

        fork
            begin
                run_mfb_data();
            end
            begin
                assert(m_info_seq.randomize());
                m_info_seq.start(p_sequencer.m_info);
            end
        join_any

        // The random channels are not needed anymore
        m_info_seq.kill();
        run_timeout_directed();

    endtask
endclass

