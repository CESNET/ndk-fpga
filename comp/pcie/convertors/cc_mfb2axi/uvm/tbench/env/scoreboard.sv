//-- scoreboard.sv: Scoreboard for verification
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


class scoreboard_cmp #(
    int unsigned ITEM_WIDTH
) extends uvm_common::comparer_base_ordered#(
    uvm_logic_vector_array::sequence_item#(ITEM_WIDTH), 
    uvm_pcie::header
);
    `uvm_component_param_utils(uvm_pcie_cc_mfb2axi::scoreboard_cmp#(ITEM_WIDTH))

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function string model_item2string(MODEL_ITEM   tr);
        uvm_pcie::completer_header hdr = new();
        uvm_pcie_axi::get_comp_hdr(hdr, tr.data);

        return hdr.convert2string();
    endfunction


    virtual function int unsigned compare(MODEL_ITEM tr_model, DUT_ITEM tr_dut);
        uvm_pcie::completer_header hdr = new();

        uvm_pcie_axi::get_comp_hdr(hdr, tr_model.data);

        //for (int unsigned it = 0; it < tr_dut.data.size(); it++) begin
        //    if ((tr_dut.data[it] ==? tr_model.data[it]) === 1'b1 ) begin
        //        return 1;
        //    end
        //end
        return hdr.compare(tr_dut);
    endfunction

endclass

class scoreboard #(ITEM_WIDTH) extends uvm_scoreboard;

    `uvm_component_utils(uvm_pcie_cc_mfb2axi::scoreboard #(ITEM_WIDTH))

    // Analysis components.
    uvm_analysis_export#(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)) analysis_imp_mfb_cc;

    uvm_pcie_cc_mfb2axi::scoreboard_cmp#(ITEM_WIDTH) cmp;

    protected uvm_pcie_mfb2avst::model#(ITEM_WIDTH, 0) m_model;

    // Contructor of scoreboard.
    function new(string name, uvm_component parent);
        super.new(name, parent);
        analysis_imp_mfb_cc = new("analysis_imp_mfb_cc", this);
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= cmp.used();
        return ret;
    endfunction

    function void build_phase(uvm_phase phase);
        m_model = uvm_pcie_mfb2avst::model #(ITEM_WIDTH, 0)::type_id::create("m_model", this);

        cmp = uvm_pcie_cc_mfb2axi::scoreboard_cmp#(ITEM_WIDTH)::type_id::create("cmp", this);
        cmp.model_tr_timeout_set(10ns);
    endfunction

    function void connect_phase(uvm_phase phase);
        analysis_imp_mfb_cc.connect(m_model.data_in.analysis_export);
        m_model.data_out.connect(cmp.analysis_imp_model);
    endfunction

    virtual function void report_phase(uvm_phase phase);
        string msg = "\n";
        msg = {msg, $sformatf("\tCompared/errors: %0d/%0d\n",  cmp.compared, cmp.errors)};

        if (this.used() == 0) begin
            `uvm_info(get_type_name(), $sformatf("%s\n\n\t---------------------------------------\n\t----     VERIFICATION SUCCESS      ----\n\t---------------------------------------", msg), UVM_NONE)
        end else begin
            `uvm_info(get_type_name(), $sformatf("%s\n\n\t---------------------------------------\n\t----     VERIFICATION FAIL      ----\n\t---------------------------------------", msg), UVM_NONE)
        end

    endfunction

endclass
