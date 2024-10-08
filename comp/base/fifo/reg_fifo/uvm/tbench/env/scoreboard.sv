// scoreboard.sv: Scoreboard for verification
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class scoreboard #(DATA_WIDTH, ITEMS) extends uvm_scoreboard;
    `uvm_component_utils(uvm_fifo_registered::scoreboard #(DATA_WIDTH, ITEMS))

    // Analysis components.
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(DATA_WIDTH)) analysis_imp_mvb_rx;
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(DATA_WIDTH)) analysis_imp_mvb_tx;

    // Comparer instance
    uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item #(DATA_WIDTH)) cmp;

    // Model instance
    uvm_pipe::model #(DATA_WIDTH) m_pipe_model;

    // Contructor of scoreboard.
    function new(string name, uvm_component parent);
        super.new(name, parent);

        analysis_imp_mvb_rx     = new("analysis_imp_mvb_rx", this);
        analysis_imp_mvb_tx     = new("analysis_imp_mvb_tx", this);
    endfunction

    function int unsigned success();
        int unsigned ret = 1;
        ret &= cmp.success();
        return ret;
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= cmp.used();
        return ret;
    endfunction

    function void build_phase(uvm_phase phase);
        cmp = uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item #(DATA_WIDTH))::type_id::create("cmp", this);
        cmp.model_tr_timeout_set(200us);

        m_pipe_model = uvm_pipe::model #(DATA_WIDTH)::type_id::create("m_pipe_model", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        // Connects input data to the input of the model
        analysis_imp_mvb_rx       .connect(m_pipe_model.model_mvb_in.analysis_export);
        // Connects output data of the models
        m_pipe_model.model_mvb_out.connect(cmp.analysis_imp_model);
        // Connects output data of the DUT
        analysis_imp_mvb_tx       .connect(cmp.analysis_imp_dut);
    endfunction

    function void report_phase(uvm_phase phase);
        string msg = "\n";

        if (this.success() && this.used() == 0) begin
            `uvm_info(get_type_name(), {msg, "\n\n\t---------------------------------------\n\t----     VERIFICATION SUCCESS      ----\n\t---------------------------------------"}, UVM_NONE)
        end else begin
            `uvm_info(get_type_name(), {msg, "\n\n\t---------------------------------------\n\t----     VERIFICATION FAILED       ----\n\t---------------------------------------"}, UVM_NONE)
        end
    endfunction
endclass
