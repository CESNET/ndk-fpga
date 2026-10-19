// sequence.sv: Virtual sequence for packet_delayer verification
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
// SPDX-License-Identifier: BSD-3-Clause

// Optional reset, then packet_count data packets and packet_count {META, TS}
// transactions in parallel (the RX agent pairs them 1:1).
//
// The defaults come from the test package; a test may change the public
// fields before start(). After body() packet_count holds the number of
// packets actually sent (used by the test to drain).
class virt_sequence extends uvm_sequence;
    `uvm_object_utils(test::virt_sequence)
    `uvm_declare_p_sequencer(vsqr_t)

    // Number of packets: random in [packet_count_min:packet_count_max] when
    // packet_count is 0, otherwise exactly packet_count
    int unsigned         packet_count     = 0;
    int unsigned         packet_count_min = PACKET_COUNT_MIN;
    int unsigned         packet_count_max = PACKET_COUNT_MAX;
    // Timestamp step range (see uvm_packet_delayer::sequence_meta)
    int unsigned         ts_min           = TS_MIN;
    int unsigned         ts_max           = TS_MAX;
    // TS_FORMAT = 1: first absolute timestamp accumulator value
    logic [TS_WIDTH-1:0] ts_start_value   = '0;
    // 0 = skip the DUT reset (the second phase of the TIME_RESET test)
    bit                  do_reset         = 1;

    uvm_reset::sequence_reset                             m_reset_pulse;
    uvm_reset::sequence_run                               m_reset_run;
    uvm_logic_vector_array::sequence_simple #(ITEM_WIDTH) m_mfb_data_sq;
    uvm_packet_delayer::sequence_meta #(META_WIDTH, TS_WIDTH, EXTENDED_META_WIDTH, TS_FORMAT) m_mfb_meta_sq;

    function new(string name = "virt_sequence");
        super.new(name);
    endfunction

    // 20-clock reset pulse followed by 20 clocks of RESET = 0
    task run_reset();
        m_reset_pulse = uvm_reset::sequence_reset::type_id::create("m_reset_pulse");
        m_reset_pulse.length_min = 20;
        m_reset_pulse.length_max = 20;
        m_reset_pulse.randomize();
        m_reset_pulse.start(p_sequencer.m_reset_sqr);

        m_reset_run = uvm_reset::sequence_run::type_id::create("m_reset_run");
        m_reset_run.length_min = 20;
        m_reset_run.length_max = 20;
        m_reset_run.randomize();
        m_reset_run.start(p_sequencer.m_reset_sqr);
    endtask

    // packet_count data packets of random size
    task run_mfb_data();
        m_mfb_data_sq = uvm_logic_vector_array::sequence_simple #(ITEM_WIDTH)::type_id::create("m_mfb_data_sq");
        m_mfb_data_sq.cfg = new();
        m_mfb_data_sq.cfg.array_size_set(FRAME_SIZE_MIN, FRAME_SIZE_MAX);
        // The sequence constrains its count to [min:max]; pin both to packet_count
        m_mfb_data_sq.transaction_count_min = packet_count;
        m_mfb_data_sq.transaction_count_max = packet_count;
        if (!m_mfb_data_sq.randomize()) begin
            `uvm_fatal(get_type_name(), $sformatf("Data sequence randomize() failed for packet_count=%0d",
                       packet_count))
        end
        m_mfb_data_sq.do_not_randomize = 1;
        m_mfb_data_sq.start(p_sequencer.m_mfb_data_sqr);
    endtask

    // packet_count {META, TS} transactions
    task run_mfb_meta();
        m_mfb_meta_sq = uvm_packet_delayer::sequence_meta #(
            META_WIDTH, TS_WIDTH, EXTENDED_META_WIDTH, TS_FORMAT
        )::type_id::create("m_mfb_meta_sq");
        m_mfb_meta_sq.transaction_count = packet_count;
        m_mfb_meta_sq.ts_min            = ts_min;
        m_mfb_meta_sq.ts_max            = ts_max;
        m_mfb_meta_sq.ts_abs_max        = TS_ABS_MAX;
        m_mfb_meta_sq.start_value       = ts_start_value;
        m_mfb_meta_sq.start(p_sequencer.m_mfb_meta_sqr);
    endtask

    task body();
        if (packet_count == 0) begin
            packet_count = $urandom_range(packet_count_min, packet_count_max);
        end
        `uvm_info(get_type_name(), $sformatf("Generating %0d data/meta packet pairs (ts step %0d..%0d)",
                  packet_count, ts_min, ts_max), UVM_LOW)

        if (do_reset) begin
            run_reset();
        end

        fork
            run_mfb_data();
            run_mfb_meta();
        join
    endtask

endclass
