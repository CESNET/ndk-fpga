// scoreboard.sv: Scoreboard for verification
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class scoreboard #(int unsigned MVB_ITEM_WIDTH, int unsigned RX_STREAMS) extends uvm_scoreboard;
    `uvm_component_param_utils(uvm_mvb_merge_streams::scoreboard #(MVB_ITEM_WIDTH, RX_STREAMS))

    // RX analysis exports
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(MVB_ITEM_WIDTH)) analysis_export_rx_mvb[RX_STREAMS];

    // TX analysis exports
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(MVB_ITEM_WIDTH)) analysis_export_tx_mvb;

    // Comparers
    uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item #(MVB_ITEM_WIDTH)) comparer[RX_STREAMS];

    // Stream splitter
    stream_splitter #(MVB_ITEM_WIDTH, RX_STREAMS) m_stream_splitter;

    // Contructor
    function new(string name = "scoreboard", uvm_component parent = null);
        super.new(name, parent);

        for (int unsigned i = 0; i < RX_STREAMS; i++) begin
            analysis_export_rx_mvb[i] = new($sformatf("analysis_export_rx_mvb_%0d", i), this);
        end
        analysis_export_tx_mvb = new("analysis_export_tx_mvb", this);
    endfunction

    function int unsigned success();
        int unsigned result = 1;
        for (int unsigned i = 0; i < RX_STREAMS; i++) begin
            result &= comparer[i].success();
        end
        return result;
    endfunction

    function int unsigned used();
        int unsigned result = 0;
        for (int unsigned i = 0; i < RX_STREAMS; i++) begin
            result |= comparer[i].used();
        end
        return result;
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        for (int unsigned i = 0; i < RX_STREAMS; i++) begin
            comparer[i] = uvm_common::comparer_ordered #(
                uvm_logic_vector::sequence_item #(MVB_ITEM_WIDTH))::type_id::create($sformatf("comparer_%0d", i), this);
            comparer[i].model_tr_timeout_set(200us);
        end

        m_stream_splitter = stream_splitter #(MVB_ITEM_WIDTH, RX_STREAMS)::type_id::create("m_stream_splitter", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);

        // RX => Comparers
        for (int unsigned i = 0; i < RX_STREAMS; i++) begin
            analysis_export_rx_mvb[i].connect(comparer[i].analysis_imp_model);
        end

        // TX -> Stream splitter => Comparers
        for (int unsigned i = 0; i < RX_STREAMS; i++) begin
            analysis_export_tx_mvb.connect(m_stream_splitter.analysis_export);
            m_stream_splitter.analysis_port[i].connect(comparer[i].analysis_imp_dut);
        end
    endfunction

    function void report_phase(uvm_phase phase);
        super.report_phase(phase);

        if (this.success() && this.used() == 0) begin
            `uvm_info(
                get_type_name(),
                // verilog_lint: waive line-length
                "\n\n\t---------------------------------------\n\t----     VERIFICATION SUCCESS      ----\n\t---------------------------------------",
                UVM_NONE)
        end else begin
            `uvm_info(get_type_name(),
                      "\n\n\t---------------------------------------\n\t----     VERIFICATION FAILED       ----\n\t---------------------------------------"
                          ,
                      UVM_NONE)
        end
    endfunction

endclass
