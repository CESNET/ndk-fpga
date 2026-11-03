// scoreboard.sv: Scoreboard for verification
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
// SPDX-License-Identifier: BSD-3-Clause

// RX monitors -> reference model -> time-aware comparers <- TX monitors.
// Checks bit-exact data/metadata AND the exact release time of every packet.
//
// The final verdict ("VERIFICATION SUCCESS" is what multi_ver looks for)
// requires both comparers to succeed, nothing to be left pending AND no
// UVM_ERROR / UVM_FATAL anywhere in the test (drain timeout, PAUSE_REQUEST
// check, ...). Checks of other components must therefore be reported before
// report_phase (in run_phase or check_phase).
class scoreboard #(
    int unsigned ITEM_WIDTH,
    int unsigned META_WIDTH,
    int unsigned EXTENDED_META_WIDTH,
    int unsigned TS_WIDTH,
    int unsigned TS_FORMAT,
    time         CLK_PERIOD,
    int unsigned PIPE_LAT,
    int unsigned ARRIV_LAT,
    int unsigned GAP_TIME
) extends uvm_scoreboard;
    `uvm_component_param_utils(uvm_packet_delayer::scoreboard #(
        ITEM_WIDTH, META_WIDTH, EXTENDED_META_WIDTH, TS_WIDTH, TS_FORMAT, CLK_PERIOD,
        PIPE_LAT, ARRIV_LAT, GAP_TIME))

    // Inputs (RX monitors)
    uvm_analysis_export #(uvm_logic_vector_array::sequence_item #(ITEM_WIDTH))    analysis_imp_mfb_rx_data;
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(EXTENDED_META_WIDTH)) analysis_imp_mfb_rx_meta;

    // Time-aware comparers (their DUT inputs are connected by the env)
    uvm_packet_delayer::cmp_time_data #(ITEM_WIDTH) data_cmp;
    uvm_packet_delayer::cmp_time_meta #(META_WIDTH) meta_cmp;

    uvm_packet_delayer::model #(
        ITEM_WIDTH, META_WIDTH, EXTENDED_META_WIDTH, TS_WIDTH, TS_FORMAT, CLK_PERIOD,
        PIPE_LAT, ARRIV_LAT, GAP_TIME
    ) m_model;

    function new(string name, uvm_component parent);
        super.new(name, parent);

        analysis_imp_mfb_rx_data = new("analysis_imp_mfb_rx_data", this);
        analysis_imp_mfb_rx_meta = new("analysis_imp_mfb_rx_meta", this);
    endfunction

    // ------------------------------------------------------------------------
    // Status used by the tests (drain) and by report_phase

    // Number of TIME_RESET assertions observed by the model
    function int unsigned time_reset_count();
        return m_model.time_reset_count();
    endfunction

    // Number of packets the model has consumed from the RX monitors so far
    function int unsigned received_count();
        return m_model.received_count();
    endfunction

    // Number of packets matched by BOTH comparers so far
    function int unsigned compared_count();
        return (data_cmp.compared < meta_cmp.compared) ? data_cmp.compared : meta_cmp.compared;
    endfunction

    // 1 = both comparers without error
    function bit success();
        return data_cmp.success() && meta_cmp.success();
    endfunction

    // 1 = something is still waiting in the model or in a comparer
    function bit used();
        return data_cmp.used() || meta_cmp.used() || m_model.used();
    endfunction

    // ------------------------------------------------------------------------
    // Phases

    function void build_phase(uvm_phase phase);
        // Runtime knob: time_check_enable (1 = default, 0 = data-only)
        bit time_check_enable = 1;

        void'(uvm_config_db#(bit)::get(this, "", "time_check_enable", time_check_enable));

        m_model = uvm_packet_delayer::model #(
            ITEM_WIDTH, META_WIDTH, EXTENDED_META_WIDTH, TS_WIDTH, TS_FORMAT, CLK_PERIOD,
            PIPE_LAT, ARRIV_LAT, GAP_TIME
        )::type_id::create("m_model", this);

        data_cmp = uvm_packet_delayer::cmp_time_data #(ITEM_WIDTH)::type_id::create(
            "data_cmp", this);
        meta_cmp = uvm_packet_delayer::cmp_time_meta #(META_WIDTH)::type_id::create(
            "meta_cmp", this);

        data_cmp.time_check_enable = time_check_enable;
        meta_cmp.time_check_enable = time_check_enable;
        // The model is re-timed: it writes both items of a packet at its
        // predicted EOF release time. This is up to one clock after the DUT item
        // (the DUT meta item is stamped at the SOF, and a packet released in the
        // same MFB word as the previous one is written after the previous EOF),
        // and a zero model timeout would race with the DUT item.
        data_cmp.model_tr_timeout_set(2 * CLK_PERIOD);
        meta_cmp.model_tr_timeout_set(2 * CLK_PERIOD);

        `uvm_info(get_type_name(), $sformatf("time_check_enable = %0d", time_check_enable), UVM_LOW)
    endfunction

    function void connect_phase(uvm_phase phase);
        analysis_imp_mfb_rx_data.connect(m_model.data_in.analysis_export);
        analysis_imp_mfb_rx_meta.connect(m_model.meta_in.analysis_export);

        m_model.data_out.connect(data_cmp.analysis_imp_model);
        m_model.meta_out.connect(meta_cmp.analysis_imp_model);
    endfunction

    function void report_phase(uvm_phase phase);
        uvm_report_server rs = uvm_report_server::get_server();
        int unsigned      errors;

        errors = rs.get_severity_count(UVM_ERROR) + rs.get_severity_count(UVM_FATAL);

        `uvm_info(get_type_name(), $sformatf(
                  {"\n\tTime check summary:",
                   "\n\t  data: max delta %s, %0d time errors",
                   "\n\t  meta: max delta %s, %0d time errors"},
                  data_cmp.delta2string(data_cmp.max_delta_get()), data_cmp.time_errors_get(),
                  meta_cmp.delta2string(meta_cmp.max_delta_get()), meta_cmp.time_errors_get()), UVM_LOW)

        if (success() && !used() && (errors == 0)) begin
            `uvm_info(get_type_name(), {"\n\n\t---------------------------------------",
                                        "\n\t----     VERIFICATION SUCCESS      ----",
                                        "\n\t---------------------------------------"}, UVM_NONE)
        end else begin
            `uvm_info(get_type_name(), $sformatf({"\n\n\t---------------------------------------",
                                                  "\n\t----     VERIFICATION FAIL         ----",
                                                  "\n\t---------------------------------------",
                                                  "\n\t UVM_ERROR/UVM_FATAL: %0d, pending: %0d",
                                                  "\n\t DATA: %s\n\t META: %s"},
                                                 errors, used(), data_cmp.info(0), meta_cmp.info(0)), UVM_NONE)
        end
    endfunction
endclass
