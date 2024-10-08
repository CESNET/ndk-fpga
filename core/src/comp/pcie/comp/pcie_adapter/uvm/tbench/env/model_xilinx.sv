//-- model.sv: Model of implementation
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause 

class model_xilinx #(CQ_MFB_ITEM_WIDTH, CC_MFB_ITEM_WIDTH, RQ_MFB_ITEM_WIDTH, RC_MFB_ITEM_WIDTH, AXI_CQUSER_WIDTH, AXI_CCUSER_WIDTH, AXI_RCUSER_WIDTH, AXI_RQUSER_WIDTH, RQ_MFB_META_W, RC_MFB_META_W, CQ_MFB_META_W, CC_MFB_META_W) 
extends model_base #(CQ_MFB_ITEM_WIDTH, CC_MFB_ITEM_WIDTH, RQ_MFB_ITEM_WIDTH, RC_MFB_ITEM_WIDTH, RQ_MFB_META_W, RC_MFB_META_W, CQ_MFB_META_W, CC_MFB_META_W);

    `uvm_component_param_utils(uvm_pcie_adapter::model_xilinx#(CQ_MFB_ITEM_WIDTH, CC_MFB_ITEM_WIDTH, RQ_MFB_ITEM_WIDTH, RC_MFB_ITEM_WIDTH, AXI_CQUSER_WIDTH, AXI_CCUSER_WIDTH, AXI_RCUSER_WIDTH, AXI_RQUSER_WIDTH, RQ_MFB_META_W, RC_MFB_META_W, CQ_MFB_META_W, CC_MFB_META_W))
    
    // Model inputs
    uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item #(CQ_MFB_ITEM_WIDTH)) axi_cq_data_in;
    uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item #(RC_MFB_ITEM_WIDTH)) axi_rc_data_in;

    uvm_analysis_port #(uvm_logic_vector_array::sequence_item #(CC_MFB_ITEM_WIDTH))   axi_cc_data_out;
    uvm_analysis_port #(uvm_logic_vector_array::sequence_item #(RQ_MFB_ITEM_WIDTH))   axi_rq_data_out;

    function new(string name = "model_xilinx", uvm_component parent = null);
        super.new(name, parent);

        axi_cq_data_in  = new("axi_cq_data_in" , this);
        axi_rc_data_in  = new("axi_rc_data_in" , this);

        axi_cc_data_out = new("axi_cc_data_out", this);
        axi_rq_data_out = new("axi_rq_data_out", this);

    endfunction

    task run_cc();
        uvm_logic_vector_array::sequence_item #(CC_MFB_ITEM_WIDTH) tr_mfb_cc_data_in;
        forever begin
            mfb_cc_data_in.get(tr_mfb_cc_data_in);
            axi_cc_data_out.write(tr_mfb_cc_data_in);
        end
    endtask

    task run_cq();
        uvm_logic_vector_array::sequence_item #(CQ_MFB_ITEM_WIDTH) tr_axi_cq_data_in;
        forever begin
            axi_cq_data_in.get(tr_axi_cq_data_in);
            mfb_cq_data_out.write(tr_axi_cq_data_in);
        end
    endtask

    task run_rc();
        uvm_logic_vector_array::sequence_item #(RC_MFB_ITEM_WIDTH) tr_axi_rc_data_in;
        forever begin
            axi_rc_data_in.get(tr_axi_rc_data_in);
            mfb_rc_data_out.write(tr_axi_rc_data_in);
        end
    endtask

    task run_rq();
        uvm_logic_vector_array::sequence_item #(RQ_MFB_ITEM_WIDTH) tr_mfb_rq_data_in;

        forever begin
            mfb_rq_data_in.get(tr_mfb_rq_data_in);
            axi_rq_data_out.write(tr_mfb_rq_data_in);
        end
    endtask

    task run_phase(uvm_phase phase);
        fork
            run_cc();
            run_cq();
            run_rc();
            run_rq();
        join_none
    endtask

endclass
