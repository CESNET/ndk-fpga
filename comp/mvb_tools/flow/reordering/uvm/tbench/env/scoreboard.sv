// scoreboard.sv: Scoreboard for verification
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
// SPDX-License-Identifier: BSD-3-Clause

class cmp #(
    ITEMS,
    ITEM_WIDTH
) extends uvm_common::comparer_ordered #(uvm_mvb::sequence_item#(ITEMS, ITEM_WIDTH));
`uvm_component_param_utils(
        uvm_mvb_reordering::cmp #(
            ITEMS,
            ITEM_WIDTH
        ))

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void write_dut(uvm_mvb::sequence_item #(ITEMS, ITEM_WIDTH) tr);
        if (tr.src_rdy == 1 && tr.dst_rdy == 1) begin
            super.write_dut(tr);
        end
    endfunction

    virtual function int unsigned compare(MODEL_ITEM tr_model, DUT_ITEM tr_dut);
         return ((tr_dut.data ==? tr_model.data) === 1'b1);
    endfunction


endclass

class scoreboard #(
    int unsigned ITEMS,
    int unsigned ITEM_WIDTH,
    bit REORDERING_EN
) extends uvm_scoreboard;
    `uvm_component_param_utils(
        uvm_mvb_reordering::scoreboard #(
            ITEMS,
            ITEM_WIDTH,
            REORDERING_EN
        ))

    // RX analysis exports
    uvm_analysis_export #(uvm_mvb::sequence_item #(ITEMS, ITEM_WIDTH + $clog2(ITEMS)))    analysis_export_rx_mvb;

    // TX analysis exports
    uvm_analysis_export #(uvm_mvb::sequence_item #(ITEMS, ITEM_WIDTH))       analysis_export_tx_mvb;

    // Comparers
    cmp  #(ITEMS, ITEM_WIDTH) comparer_mvb;

    // Model
    model #(ITEMS, ITEM_WIDTH, REORDERING_EN) m_model;

    // Contructor
    function new(string name = "scoreboard", uvm_component parent = null);
        super.new(name, parent);

        analysis_export_rx_mvb      = new("analysis_export_rx_mvb", this);
        analysis_export_tx_mvb      = new("analysis_export_tx_mvb", this);
    endfunction

    function int unsigned success();
        int unsigned result = 1;
        result &= comparer_mvb     .success();
        return result;
    endfunction

    function int unsigned used();
        int unsigned result = 0;
        result |= comparer_mvb     .used();
        return result;
    endfunction

    function void build_phase(uvm_phase phase);
        // verilog_lint: waive line-length
        comparer_mvb      = cmp  #(ITEMS, ITEM_WIDTH) ::type_id::create("comparer_mvb", this);
        comparer_mvb     .model_tr_timeout_set(200us);

        m_model = model #(ITEMS, ITEM_WIDTH, REORDERING_EN)::type_id::create("m_model", this);

    endfunction

    function void connect_phase(uvm_phase phase);
        // RX MVB -> Meta splitter
        analysis_export_rx_mvb.connect(m_model.model_mvb_in.analysis_export);

        m_model.model_mvb_out.connect(comparer_mvb.analysis_imp_model);

        // TX MFB -> MVB comparer
        analysis_export_tx_mvb.connect(comparer_mvb.analysis_imp_dut);
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
