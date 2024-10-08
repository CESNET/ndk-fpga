// scoreboard.sv: Scoreboard for verification
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class scoreboard #(HEADER_SIZE, MFB_ITEM_WIDTH, MVB_ITEM_WIDTH, VERBOSITY) extends uvm_scoreboard;
    `uvm_component_param_utils(uvm_superunpacketer::scoreboard #(HEADER_SIZE, MFB_ITEM_WIDTH, MVB_ITEM_WIDTH, VERBOSITY))

    uvm_analysis_export #(uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH))               out_data;
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(HEADER_SIZE+MVB_ITEM_WIDTH))         out_meta;

    uvm_analysis_export #(uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH))            input_data;
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(MVB_ITEM_WIDTH))                  input_mvb;

    uvm_common::comparer_ordered #(uvm_logic_vector_array::sequence_item#(MFB_ITEM_WIDTH))       data_cmp;
    uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item#(HEADER_SIZE+MVB_ITEM_WIDTH)) meta_cmp;

    model #(HEADER_SIZE, MFB_ITEM_WIDTH, MVB_ITEM_WIDTH, VERBOSITY) m_model;

    // Contructor of scoreboard.
    function new(string name, uvm_component parent);
        super.new(name, parent);

        out_data   = new("out_data", this);
        out_meta   = new("out_meta", this);
        input_data = new("input_data", this);
        input_mvb  = new("input_mvb", this);
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
        data_cmp = uvm_common::comparer_ordered #(uvm_logic_vector_array::sequence_item#(MFB_ITEM_WIDTH))::type_id::create("data_cmp", this);
        meta_cmp = uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item#(HEADER_SIZE+MVB_ITEM_WIDTH))::type_id::create("meta_cmp", this);

        data_cmp.compared_tr_timeout_set(50us);
        meta_cmp.compared_tr_timeout_set(50us);
        data_cmp.model_tr_timeout_set(1ms);
        meta_cmp.model_tr_timeout_set(1ms);

        m_model = model#(HEADER_SIZE, MFB_ITEM_WIDTH, MVB_ITEM_WIDTH, VERBOSITY)::type_id::create("m_model", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        input_data.connect(m_model.input_data.analysis_export);
        input_mvb .connect(m_model.input_mvb .analysis_export);

        // processed data from the output of the model connected to the analysis fifo
        m_model.out_data.connect(data_cmp.analysis_imp_model);
        m_model.out_meta.connect(meta_cmp.analysis_imp_model);
        // connects the data from the DUT to the analysis fifo
        out_data.connect(data_cmp.analysis_imp_dut);
        out_meta.connect(meta_cmp.analysis_imp_dut);

    endfunction

    function void report_phase(uvm_phase phase);

        if (this.success() && this.used() == 0) begin
            `uvm_info(get_type_name(), "\n\n\t---------------------------------------\n\t----     VERIFICATION SUCCESS      ----\n\t---------------------------------------", UVM_NONE)
        end else begin
            `uvm_info(get_type_name(), "\n\n\t---------------------------------------\n\t----     VERIFICATION FAILED       ----\n\t---------------------------------------", UVM_NONE)
        end

    endfunction

endclass
