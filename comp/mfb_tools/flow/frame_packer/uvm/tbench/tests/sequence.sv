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


    endtask
endclass

