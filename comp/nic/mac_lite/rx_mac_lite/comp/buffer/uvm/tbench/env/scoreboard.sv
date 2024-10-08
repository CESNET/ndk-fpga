// scoreboard.sv: Scoreboard for verification
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class scoreboard #(MFB_ITEM_WIDTH, MFB_META_WIDTH, MFB_REGIONS, DUT_PATH) extends uvm_scoreboard;
    `uvm_component_param_utils(uvm_rx_mac_lite_buffer::scoreboard #(MFB_ITEM_WIDTH, MFB_META_WIDTH, MFB_REGIONS, DUT_PATH))

    uvm_analysis_export #(uvm_logic_vector_array::sequence_item#(MFB_ITEM_WIDTH)) analysis_imp_mfb_data;
    uvm_analysis_export #(uvm_logic_vector::sequence_item#(MFB_META_WIDTH))       analysis_imp_mfb_meta;

    uvm_analysis_export #(uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH)) out_mfb_data;
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(MFB_META_WIDTH))       out_mvb_data;

    protected uvm_common::comparer_ordered #(uvm_logic_vector_array::sequence_item#(MFB_ITEM_WIDTH)) data_cmp;
    protected uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item#(MFB_META_WIDTH))       meta_cmp;
    protected model #(MFB_ITEM_WIDTH, MFB_META_WIDTH, MFB_REGIONS, DUT_PATH) m_model;

    // Contructor of scoreboard.
    function new(string name, uvm_component parent);
        super.new(name, parent);

        analysis_imp_mfb_data = new("analysis_imp_mfb_data", this);
        analysis_imp_mfb_meta = new("analysis_imp_mfb_meta", this);

        out_mfb_data = new("out_mfb_data", this);
        out_mvb_data = new("out_mvb_data", this);
    endfunction

    function int unsigned success();
        int unsigned ret = 1;
        ret &= data_cmp.success();
        ret &= meta_cmp.success();
        return ret;
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= data_cmp.used();
        ret |= meta_cmp.used();
        return ret;
    endfunction


    function void build_phase(uvm_phase phase);
        m_model = model#(MFB_ITEM_WIDTH, MFB_META_WIDTH, MFB_REGIONS, DUT_PATH)::type_id::create("m_model", this);

        data_cmp = uvm_common::comparer_ordered #(uvm_logic_vector_array::sequence_item#(MFB_ITEM_WIDTH))::type_id::create("data_cmp", this);
        meta_cmp = uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item#(MFB_META_WIDTH))::type_id::create("meta_cmp", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        // connects input data to the input of the model
        analysis_imp_mfb_data.connect(m_model.input_mfb_data.analysis_export);
        analysis_imp_mfb_meta.connect(m_model.input_mfb_meta.analysis_export);

        // processed data from the output of the model connected to the analysis fifo
        m_model.out_mfb_data.connect(data_cmp.analysis_imp_model);
        m_model.out_mvb_data.connect(meta_cmp.analysis_imp_model);

        // connects the data from the DUT to the analysis fifo
        out_mfb_data.connect(data_cmp.analysis_imp_dut);
        out_mvb_data.connect(meta_cmp.analysis_imp_dut);
    endfunction

    function void report_phase(uvm_phase phase);
        string msg = "\n";
        msg = {msg, $sformatf("\n\tMODEL %s\n", m_model.info())};
        msg = {msg, $sformatf("\n\tDATA info %s", data_cmp.info())};
        msg = {msg, $sformatf("\n\tMETA info %s", meta_cmp.info())};

        if (this.success() && this.used() == 0) begin
            `uvm_info(get_type_name(), {msg, "\n\n\t---------------------------------------\n\t----     VERIFICATION SUCCESS      ----\n\t---------------------------------------"}, UVM_NONE)
        end else begin
            `uvm_info(get_type_name(), {msg, "\n\n\t---------------------------------------\n\t----     VERIFICATION FAILED       ----\n\t---------------------------------------"}, UVM_NONE)
        end
    endfunction

endclass
