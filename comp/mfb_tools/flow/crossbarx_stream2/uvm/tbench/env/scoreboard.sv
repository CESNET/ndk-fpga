// scoreboard.sv: Scoreboard for verification
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class scoreboard #(RX_MFB_ITEM_W, RX_MVB_ITEM_W, USERMETA_W, MOD_W) extends uvm_scoreboard;
    `uvm_component_param_utils(uvm_mfb_crossbarx_stream2::scoreboard #(RX_MFB_ITEM_W, RX_MVB_ITEM_W, USERMETA_W, MOD_W))

    uvm_analysis_export #(uvm_logic_vector_array::sequence_item #(RX_MFB_ITEM_W)) out_data;
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(USERMETA_W))          out_meta;

    uvm_mfb_crossbarx_stream2::cxs2_comparer #(uvm_logic_vector_array::sequence_item#(RX_MFB_ITEM_W)) data_cmp;
    uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item#(USERMETA_W)) meta_cmp;

    uvm_analysis_export #(uvm_logic_vector_array::sequence_item#(RX_MFB_ITEM_W)) analysis_imp_mfb_data;
    uvm_analysis_export #(uvm_logic_vector::sequence_item#(USERMETA_W))          analysis_imp_mfb_meta;
    uvm_analysis_export #(uvm_logic_vector::sequence_item#(RX_MVB_ITEM_W))       analysis_imp_mvb_data;

    model #(RX_MFB_ITEM_W, RX_MVB_ITEM_W, USERMETA_W, MOD_W) m_model;

    // Contructor of scoreboard.
    function new(string name, uvm_component parent);
        super.new(name, parent);

        out_data   = new("out_data", this);
        out_meta   = new("out_meta", this);

        analysis_imp_mfb_data = new("analysis_imp_mfb_data", this);
        analysis_imp_mfb_meta = new("analysis_imp_mfb_meta", this);
        analysis_imp_mvb_data = new("analysis_imp_mvb_data", this);
    endfunction

    function int unsigned success();
        int unsigned ret = 0;
        ret |= data_cmp.success();
        ret |= meta_cmp.success();
        return ret;
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= data_cmp.used();
        ret |= meta_cmp.used();
        return ret;
    endfunction


    function void build_phase(uvm_phase phase);
        m_model = model#(RX_MFB_ITEM_W, RX_MVB_ITEM_W, USERMETA_W, MOD_W)::type_id::create("m_model", this);

        data_cmp = uvm_mfb_crossbarx_stream2::cxs2_comparer #(uvm_logic_vector_array::sequence_item#(RX_MFB_ITEM_W))::type_id::create("data_cmp", this);
        meta_cmp = uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item#(USERMETA_W))::type_id::create("meta_cmp", this);

        data_cmp.model_tr_timeout_set(100000ns);
        meta_cmp.model_tr_timeout_set(100000ns);
    endfunction

    function void connect_phase(uvm_phase phase);

        // connects input data to the input of the model
        analysis_imp_mfb_data.connect(m_model.input_data.analysis_export);
        analysis_imp_mfb_meta.connect(m_model.input_meta.analysis_export);
        analysis_imp_mvb_data.connect(m_model.input_mvb.analysis_export);

        // processed data from the output of the model connected to the analysis fifo
        m_model.out_data.connect(data_cmp.analysis_imp_model);
        m_model.out_meta.connect(meta_cmp.analysis_imp_model);
        // connects the data from the DUT to the analysis fifo
        out_data.connect(data_cmp.analysis_imp_dut);
        out_meta.connect(meta_cmp.analysis_imp_dut);

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
