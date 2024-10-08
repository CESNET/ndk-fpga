//-- scoreboard.sv: Scoreboard for verification
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class scoreboard #(ITEM_WIDTH, META_WIDTH) extends uvm_scoreboard;

    `uvm_component_utils(uvm_pcie_avst2mfb::scoreboard #(ITEM_WIDTH, META_WIDTH))
    // Analysis components.
    uvm_analysis_export #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)) analysis_imp_avst_data;
    uvm_analysis_export #(uvm_logic_vector::sequence_item#(META_WIDTH))       analysis_imp_avst_meta;
    uvm_analysis_export #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH))    analysis_imp_mfb_data;
    uvm_analysis_export #(uvm_logic_vector::sequence_item#(META_WIDTH))          analysis_imp_mfb_meta;

    uvm_common::comparer_ordered #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)) data_cmp;
    uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item#(META_WIDTH))       meta_cmp;

    uvm_pcie_mfb2avst::model#(ITEM_WIDTH, META_WIDTH) m_model;

    // Contructor of scoreboard.
    function new(string name, uvm_component parent);
        super.new(name, parent);
        analysis_imp_mfb_data  = new("analysis_imp_mfb_data", this);
        analysis_imp_mfb_meta  = new("analysis_imp_mfb_meta", this);
        analysis_imp_avst_data = new("analysis_imp_avst_data", this);
        analysis_imp_avst_meta = new("analysis_imp_avst_meta", this);
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= data_cmp.used();
        ret |= meta_cmp.used();
        ret |= data_cmp.errors != 0;
        ret |= meta_cmp.errors != 0;
        return ret;
    endfunction

    function void build_phase(uvm_phase phase);
        m_model = uvm_pcie_mfb2avst::model #(ITEM_WIDTH, META_WIDTH)::type_id::create("m_model", this);

        data_cmp = uvm_common::comparer_ordered #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH))::type_id::create("data_cmp", this);
        meta_cmp = uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item#(META_WIDTH))::type_id::create("meta_cmp", this);

    endfunction

    function void connect_phase(uvm_phase phase);
        analysis_imp_avst_data.connect(m_model.data_in.analysis_export);
        analysis_imp_avst_meta.connect(m_model.meta_in.analysis_export);

        m_model.data_out.connect(data_cmp.analysis_imp_model);
        m_model.meta_out.connect(meta_cmp.analysis_imp_model);

        analysis_imp_mfb_data.connect(data_cmp.analysis_imp_dut);
        analysis_imp_mfb_meta.connect(meta_cmp.analysis_imp_dut);
    endfunction

    virtual function void report_phase(uvm_phase phase);
        string msg = "\n";
        msg = {msg, $sformatf("\tDATA Compared/errors: %0d/%0d\n\tMETA Compared/errors: %0d/%0d\n",  data_cmp.compared, data_cmp.errors, meta_cmp.compared, meta_cmp.errors)};

        if (this.used() == 0) begin
            `uvm_info(get_type_name(), $sformatf("%s\n\n\t---------------------------------------\n\t----     VERIFICATION SUCCESS      ----\n\t---------------------------------------", msg), UVM_NONE)
        end else begin
            `uvm_info(get_type_name(), $sformatf("%s\n\n\t---------------------------------------\n\t----     VERIFICATION FAIL      ----\n\t---------------------------------------", msg), UVM_NONE)
        end

    endfunction

endclass
