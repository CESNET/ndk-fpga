//-- scoreboard.sv: Scoreboard for verification
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author:   Oliver Gurka <xgurka00@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class scoreboard #(ITEMS, ITEM_WIDTH, RX_MVB_CNT) extends uvm_scoreboard;

    `uvm_component_utils(uvm_mvb_mux::scoreboard #(ITEMS, ITEM_WIDTH, RX_MVB_CNT))

    // Analysis components.
    uvm_analysis_export #(uvm_mvb::sequence_item#(ITEMS, ITEM_WIDTH)) analysis_imp_mvb_rx[RX_MVB_CNT - 1 : 0];
    uvm_analysis_export #(uvm_logic_vector::sequence_item#($clog2(RX_MVB_CNT))) analysis_imp_mvb_sel_rx;
    uvm_analysis_export #(uvm_mvb::sequence_item#(ITEMS, ITEM_WIDTH)) analysis_imp_mvb_tx;

    uvm_mvb_mux::mvb_comparer #(ITEMS, ITEM_WIDTH) comparer;

    model#(ITEMS, ITEM_WIDTH, RX_MVB_CNT) m_model;

    local int unsigned compared = 0;
    local int unsigned errors   = 0;

    // Contructor of scoreboard.
    function new(string name, uvm_component parent);
        super.new(name, parent);

        for (int port = 0; port < RX_MVB_CNT; port++) begin
            analysis_imp_mvb_rx[port] = new($sformatf("analysis_imp_rx_%0d", port), this);
        end
        analysis_imp_mvb_sel_rx = new("analysis_imp_sel_rx", this);
        analysis_imp_mvb_tx     = new("analysis_imp_tx", this);
    endfunction

    function void build_phase(uvm_phase phase);
        m_model = model #(ITEMS, ITEM_WIDTH, RX_MVB_CNT)::type_id::create("m_model", this);

        comparer                = uvm_mvb_mux::mvb_comparer #(ITEMS, ITEM_WIDTH)::type_id::create("mvb_comparer", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        for (int port = 0; port < RX_MVB_CNT; port++) begin
            analysis_imp_mvb_rx[port].connect(m_model.model_mvb_in[port].analysis_export);
        end
        analysis_imp_mvb_sel_rx.connect(m_model.model_mvb_sel.analysis_export);
        m_model.model_mvb_out.connect(comparer.analysis_imp_model);
        analysis_imp_mvb_tx.connect(comparer.analysis_imp_dut);
    endfunction // connect_phase

    virtual function void report_phase(uvm_phase phase);
        string msg = "\n";
        msg = {msg, $sformatf("Compared/errors: %0d/%0d \n",  comparer.compared, comparer.errors)};

        if (comparer.errors == 0 && comparer.used() == 0) begin
            `uvm_info(get_type_name(), $sformatf("%s\n\n\t---------------------------------------\n\t----     VERIFICATION SUCCESS      ----\n\t---------------------------------------", msg), UVM_NONE)
        end else begin
            `uvm_info(get_type_name(), $sformatf("%s\n\n\t---------------------------------------\n\t----     VERIFICATION FAIL      ----\n\t---------------------------------------", msg), UVM_NONE)
        end

    endfunction

endclass
