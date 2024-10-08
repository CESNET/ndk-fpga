// scoreboard.sv: Scoreboard for verification
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class scoreboard #(DATA_WIDTH, STATUS_WIDTH, ITEMS, ALMOST_FULL_OFFSET, ALMOST_EMPTY_OFFSET) extends uvm_scoreboard;
    `uvm_component_utils(uvm_fifox::scoreboard #(DATA_WIDTH, STATUS_WIDTH, ITEMS, ALMOST_FULL_OFFSET, ALMOST_EMPTY_OFFSET))

    // Analysis components.
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(DATA_WIDTH)) analysis_imp_mvb_rx;

    uvm_analysis_export #(uvm_logic_vector::sequence_item #(DATA_WIDTH))     analysis_imp_mvb_tx;
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(STATUS_WIDTH+2)) analysis_imp_mvb_status;

    // Comparer instance
    uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item #(DATA_WIDTH)) cmp;
    status_comparer #(STATUS_WIDTH) status_cmp;

    // Model instance
    uvm_pipe::model #(DATA_WIDTH) m_pipe_model;
    status_model #(STATUS_WIDTH, ITEMS, ALMOST_FULL_OFFSET, ALMOST_EMPTY_OFFSET) m_status_model;

    // Contructor of scoreboard.
    function new(string name, uvm_component parent);
        super.new(name, parent);

        analysis_imp_mvb_rx     = new("analysis_imp_mvb_rx",     this);
        analysis_imp_mvb_tx     = new("analysis_imp_mvb_tx",     this);
        analysis_imp_mvb_status = new("analysis_imp_mvb_status", this);

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

        status_cmp = status_comparer #(STATUS_WIDTH)::type_id::create("status_cmp", this);
        status_cmp.model_tr_timeout_set(200us);

        m_pipe_model = uvm_pipe::model #(DATA_WIDTH)::type_id::create("m_pipe_model", this);
        m_status_model = status_model #(STATUS_WIDTH, ITEMS, ALMOST_FULL_OFFSET, ALMOST_EMPTY_OFFSET)::type_id::create("m_status_model", this);

    endfunction

    function void connect_phase(uvm_phase phase);

        // Connects input data to the input of the model
        analysis_imp_mvb_rx.connect(m_pipe_model.model_mvb_in.analysis_export);

        // Connects output data of the models
        m_pipe_model.model_mvb_out.connect(cmp       .analysis_imp_model);
        m_status_model.model_out  .connect(status_cmp.analysis_imp_model);

        // Connects output data of the DUT
        analysis_imp_mvb_tx    .connect(cmp       .analysis_imp_dut);
        analysis_imp_mvb_status.connect(status_cmp.analysis_imp_dut);

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
