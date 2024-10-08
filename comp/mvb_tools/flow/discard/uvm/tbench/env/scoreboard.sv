//-- scoreboard.sv: Scoreboard for verification
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author:   Jakub Cabal <cabal@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class scoreboard #(ITEM_WIDTH) extends uvm_scoreboard;

    `uvm_component_utils(uvm_discard::scoreboard #(ITEM_WIDTH))
    // Analysis components.
    uvm_analysis_export #(uvm_logic_vector::sequence_item#(ITEM_WIDTH+1)) analysis_imp_mvb_rx;
    uvm_analysis_export #(uvm_logic_vector::sequence_item#(ITEM_WIDTH)) analysis_imp_mvb_tx;

    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item#(ITEM_WIDTH)) dut_out_fifo;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item#(ITEM_WIDTH)) model_out_fifo;

    model#(ITEM_WIDTH) m_model;

    local int unsigned compared = 0;
    local int unsigned errors   = 0;

    // Contructor of scoreboard.
    function new(string name, uvm_component parent);
        super.new(name, parent);
        analysis_imp_mvb_rx = new("analysis_imp_mvb_rx", this);
        analysis_imp_mvb_tx = new("analysis_imp_mvb_tx", this);
        dut_out_fifo = new("dut_out_fifo", this);
        model_out_fifo = new("model_out_fifo", this);
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= (dut_out_fifo.used() != 0);
        ret |= (model_out_fifo.used() != 0);
        return ret;
    endfunction

        function void build_phase(uvm_phase phase);
        m_model = model #(ITEM_WIDTH)::type_id::create("m_model", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        analysis_imp_mvb_rx.connect(m_model.model_mvb_in.analysis_export);
        m_model.model_mvb_out.connect(model_out_fifo.analysis_export);
        analysis_imp_mvb_tx.connect(dut_out_fifo.analysis_export);
    endfunction


    task run_phase(uvm_phase phase);
        string msg;
        uvm_logic_vector::sequence_item#(ITEM_WIDTH) tr_model;
        uvm_logic_vector::sequence_item#(ITEM_WIDTH) tr_dut;

        forever begin
            string debug_msg = "";

            dut_out_fifo.get(tr_dut);
            model_out_fifo.get(tr_model);

            debug_msg = {debug_msg, $sformatf("\n\t Model MVB TR: %s\n",  tr_model.convert2string())};
            debug_msg = {debug_msg, $sformatf("\n\t DUT MVB TR: %s\n",  tr_dut.convert2string())};
            `uvm_info(this.get_full_name(), debug_msg ,UVM_MEDIUM);

            compared++;
            if (tr_model.compare(tr_dut) == 0) begin
                errors++;
                msg = $sformatf( "\nTransactions doesnt match\n\tMODEL Transaction\n%s\n\n\tDUT Transaction\n%s", tr_model.convert2string(), tr_dut.convert2string());
                `uvm_error(this.get_full_name(), msg);
            end
        end
    endtask

    virtual function void report_phase(uvm_phase phase);
        string msg = "\n";
        msg = {msg, $sformatf("Compared/errors: %0d/%0d \n",  compared, errors)};
        msg = {msg, $sformatf("Count of items inside RX fifo: %d \n",  dut_out_fifo.used())};
        msg = {msg, $sformatf("Count of items inside TX fifo: %d \n",  model_out_fifo.used())};
        msg = {msg, $sformatf("Errors : %d \n",  errors)};

        if (errors == 0 && this.used() == 0) begin
            `uvm_info(get_type_name(), $sformatf("%s\n\n\t---------------------------------------\n\t----     VERIFICATION SUCCESS      ----\n\t---------------------------------------", msg), UVM_NONE)
        end else begin
            `uvm_info(get_type_name(), $sformatf("%s\n\n\t---------------------------------------\n\t----     VERIFICATION FAIL      ----\n\t---------------------------------------", msg), UVM_NONE)
        end

    endfunction

endclass
