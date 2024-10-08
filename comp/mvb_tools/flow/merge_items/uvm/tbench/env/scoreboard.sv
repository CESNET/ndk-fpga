//-- scoreboard.sv: Scoreboard for verification
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class scoreboard #(RX0_ITEM_WIDTH, RX1_ITEM_WIDTH, TX_ITEM_WIDTH) extends uvm_scoreboard;
    `uvm_component_utils(merge_items::scoreboard #(RX0_ITEM_WIDTH, RX1_ITEM_WIDTH, TX_ITEM_WIDTH))

    // Analysis components.
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(RX0_ITEM_WIDTH)) analysis_imp_mvb_rx0;
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(RX1_ITEM_WIDTH)) analysis_imp_mvb_rx1;

    uvm_analysis_export #(uvm_logic_vector::sequence_item #(TX_ITEM_WIDTH))  analysis_imp_mvb_tx;
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(RX0_ITEM_WIDTH)) analysis_imp_mvb_tx0;
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(RX1_ITEM_WIDTH)) analysis_imp_mvb_tx1;

    uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item #(TX_ITEM_WIDTH))  cmp;
    uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item #(RX0_ITEM_WIDTH)) cmp0;
    uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item #(RX1_ITEM_WIDTH)) cmp1;

    model           #(RX0_ITEM_WIDTH, RX1_ITEM_WIDTH, TX_ITEM_WIDTH) m_model;
    uvm_pipe::model #(RX0_ITEM_WIDTH)                                m_model_pipe0;
    uvm_pipe::model #(RX1_ITEM_WIDTH)                                m_model_pipe1;

    // Contructor of scoreboard.
    function new(string name, uvm_component parent);
        super.new(name, parent);

        analysis_imp_mvb_tx  = new("analysis_imp_mvb_tx",  this);
        analysis_imp_mvb_tx0 = new("analysis_imp_mvb_tx0", this);
        analysis_imp_mvb_tx1 = new("analysis_imp_mvb_tx1", this);

        analysis_imp_mvb_rx0 = new("analysis_imp_mvb_rx0", this);
        analysis_imp_mvb_rx1 = new("analysis_imp_mvb_rx1", this);
    endfunction

    function int unsigned success();
        int unsigned ret = 0;
        ret |= cmp .success();
        ret |= cmp0.success();
        ret |= cmp1.success();
        return ret;
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= cmp .used();
        ret |= cmp0.used();
        ret |= cmp1.used();
        return ret;
    endfunction

    function void build_phase(uvm_phase phase);
        cmp  = uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item #(TX_ITEM_WIDTH)) ::type_id::create("cmp",  this);
        cmp0 = uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item #(RX0_ITEM_WIDTH))::type_id::create("cmp0", this);
        cmp1 = uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item #(RX1_ITEM_WIDTH))::type_id::create("cmp1", this);
        cmp .model_tr_timeout_set(200us);
        cmp0.model_tr_timeout_set(200us);
        cmp1.model_tr_timeout_set(200us);

        m_model       = model               #(RX0_ITEM_WIDTH, RX1_ITEM_WIDTH, TX_ITEM_WIDTH)::type_id::create("m_model",       this);
        m_model_pipe0 = uvm_pipe::model #(RX0_ITEM_WIDTH)                               ::type_id::create("m_model_pipe0", this);
        m_model_pipe1 = uvm_pipe::model #(RX1_ITEM_WIDTH)                               ::type_id::create("m_model_pipe1", this);

    endfunction

    function void connect_phase(uvm_phase phase);

        // Connects input data to the input of the models
        analysis_imp_mvb_rx0.connect(m_model      .model_mvb_in0.analysis_export);
        analysis_imp_mvb_rx1.connect(m_model      .model_mvb_in1.analysis_export);
        analysis_imp_mvb_rx0.connect(m_model_pipe0.model_mvb_in .analysis_export);
        analysis_imp_mvb_rx1.connect(m_model_pipe1.model_mvb_in .analysis_export);

        // Processed data from the output of the model connected to the analysis fifo
        m_model      .model_mvb_out.connect(cmp .analysis_imp_model);
        m_model_pipe0.model_mvb_out.connect(cmp0.analysis_imp_model);
        m_model_pipe1.model_mvb_out.connect(cmp1.analysis_imp_model);

        // Processed data from the output of the DUT connected to the analysis fifo
        analysis_imp_mvb_tx .connect(cmp .analysis_imp_dut);
        analysis_imp_mvb_tx0.connect(cmp0.analysis_imp_dut);
        analysis_imp_mvb_tx1.connect(cmp1.analysis_imp_dut);

    endfunction

    function void report_phase(uvm_phase phase);
        string msg = "\n";

        msg = {msg, $sformatf("\n\tDATA STUCK INSIDE\t\nRX0:%d, RX1:%d",  m_model.model_mvb_in0.used(), m_model.model_mvb_in1.used())};

        if (this.success() && this.used() == 0) begin
            `uvm_info(get_type_name(), {msg, "\n\n\t---------------------------------------\n\t----     VERIFICATION SUCCESS      ----\n\t---------------------------------------"}, UVM_NONE)
        end else begin
            `uvm_info(get_type_name(), {msg, "\n\n\t---------------------------------------\n\t----     VERIFICATION FAILED       ----\n\t---------------------------------------"}, UVM_NONE)
        end

    endfunction


endclass
