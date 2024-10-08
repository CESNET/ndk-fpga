//-- scoreboard.sv: Scoreboard for verification
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author:   David Beneš <xbenes52@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class scoreboard #(ITEM_WIDTH, META_WIDTH) extends uvm_scoreboard;

    `uvm_component_utils(uvm_mfb_pipe::scoreboard #(ITEM_WIDTH, META_WIDTH))

    // Analysis components //
    //Model
    uvm_analysis_export #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH))    analysis_imp_mfb_rx_data;
    uvm_analysis_export #(uvm_logic_vector::sequence_item#(META_WIDTH))          analysis_imp_mfb_rx_meta;

    //Comparer
    uvm_common::comparer_ordered #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH))  data_cmp;
    uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item#(META_WIDTH))        meta_cmp;

    model#(ITEM_WIDTH, META_WIDTH) m_model;

    // Contructor of scoreboard.
    function new(string name, uvm_component parent);
        super.new(name, parent);

        analysis_imp_mfb_rx_data = new("analysis_imp_mfb_rx_data", this);
        analysis_imp_mfb_rx_meta = new("analysis_imp_mfb_rx_meta", this);
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
        ret |= m_model.used();
        return ret;
    endfunction


    function void build_phase(uvm_phase phase);
        m_model = model #(ITEM_WIDTH, META_WIDTH)::type_id::create("m_model", this);

        data_cmp = uvm_common::comparer_ordered #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH))::type_id::create("data_cmp", this);
        meta_cmp = uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item#(META_WIDTH))::type_id::create("meta_cmp", this);
        data_cmp.model_tr_timeout_set(10ns);
        meta_cmp.model_tr_timeout_set(10ns);
    endfunction

    function void connect_phase(uvm_phase phase);
        //Input of model
        analysis_imp_mfb_rx_data.connect(m_model.data_in.analysis_export);
        analysis_imp_mfb_rx_meta.connect(m_model.meta_in.analysis_export);

        //Connect model output to comparer
        m_model.data_out.connect(data_cmp.analysis_imp_model);
        m_model.meta_out.connect(meta_cmp.analysis_imp_model);
    endfunction

    virtual function void report_phase(uvm_phase phase);

        if (this.success() && this.used() == 0) begin
            `uvm_info(get_type_name(), $sformatf("\n\n\t---------------------------------------\n\t----     VERIFICATION SUCCESS      ----\n\t---------------------------------------"), UVM_NONE)
        end else begin
            `uvm_info(get_type_name(), $sformatf("\n\n\t---------------------------------------\n\t----     VERIFICATION FAIL      ----\n\t---------------------------------------"), UVM_NONE)
        end

    endfunction
endclass
