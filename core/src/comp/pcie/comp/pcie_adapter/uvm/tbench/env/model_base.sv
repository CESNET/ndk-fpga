//-- model_base.sv: Model of implementation
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause 

class model_base #(CQ_MFB_ITEM_WIDTH, CC_MFB_ITEM_WIDTH, RQ_MFB_ITEM_WIDTH, RC_MFB_ITEM_WIDTH, RQ_MFB_META_W, RC_MFB_META_W, CQ_MFB_META_W, CC_MFB_META_W) extends uvm_component;

    `uvm_component_param_utils(uvm_pcie_adapter::model_base#(CQ_MFB_ITEM_WIDTH, CC_MFB_ITEM_WIDTH, RQ_MFB_ITEM_WIDTH, RC_MFB_ITEM_WIDTH, RQ_MFB_META_W, RC_MFB_META_W, CQ_MFB_META_W, CC_MFB_META_W))

    // Model inputs
    uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item #(CC_MFB_ITEM_WIDTH)) mfb_cc_data_in;
    uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item #(RQ_MFB_ITEM_WIDTH)) mfb_rq_data_in;

    uvm_analysis_port #(uvm_logic_vector_array::sequence_item #(RC_MFB_ITEM_WIDTH))   mfb_rc_data_out;
    uvm_analysis_port #(uvm_logic_vector_array::sequence_item #(CQ_MFB_ITEM_WIDTH))   mfb_cq_data_out;

    function new(string name = "model_base", uvm_component parent = null);
        super.new(name, parent);

        mfb_cc_data_in  = new("mfb_cc_data_in" , this);
        mfb_rq_data_in  = new("mfb_rq_data_in" , this);

        mfb_rc_data_out = new("mfb_rc_data_out", this);
        mfb_cq_data_out = new("mfb_cq_data_out", this);

    endfunction

endclass
