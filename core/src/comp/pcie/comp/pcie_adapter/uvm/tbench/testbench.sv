//-- tbench.sv: Testbench
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import uvm_pkg::*;
`include "uvm_macros.svh"
import test::*;

module testbench;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Signals
    logic CLK = 0;
    logic RST = 0;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Interfaces
    reset_if  reset(CLK);
    // For Intel (AVALON)
    avst_if #(CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, CQ_MFB_ITEM_WIDTH, AVST_DOWN_META_W) avst_down(CLK);
    avst_if #(CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, CC_MFB_ITEM_WIDTH, AVST_UP_META_W)   avst_up(CLK);
    // For Credit control
    crdt_if crdt_down(CLK);
    crdt_if crdt_up(CLK);
    // For Xilinx (AXI)
    axi_if #(AXI_DATA_WIDTH, AXI_CQUSER_WIDTH) cq_axi(CLK);
    axi_if #(AXI_DATA_WIDTH, AXI_CCUSER_WIDTH) cc_axi(CLK);
    axi_if #(AXI_DATA_WIDTH, AXI_RCUSER_WIDTH) rc_axi(CLK);
    axi_if #(AXI_DATA_WIDTH, AXI_RQUSER_WIDTH) rq_axi(CLK);
    // For Intel and Xilinx (MFB)
    mfb_if #(RQ_MFB_REGIONS, RQ_MFB_REGION_SIZE, RQ_MFB_BLOCK_SIZE, RQ_MFB_ITEM_WIDTH, RQ_MFB_META_W)  rq_mfb(CLK);
    mfb_if #(RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, RC_MFB_ITEM_WIDTH, RC_MFB_META_W)  rc_mfb(CLK);
    mfb_if #(CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, CQ_MFB_ITEM_WIDTH, CQ_MFB_META_W)  cq_mfb(CLK);
    mfb_if #(CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, CC_MFB_ITEM_WIDTH, CC_MFB_META_W)  cc_mfb(CLK);
    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Define clock period
    always #(CLK_PERIOD) CLK = ~CLK;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Start of tests
    initial begin
        uvm_root m_root;
        // Configuration of database
        uvm_config_db#(virtual reset_if)::set(null, "", "vif_reset", reset);
        // AVALON interface
        uvm_config_db#(virtual avst_if #(CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, CQ_MFB_ITEM_WIDTH, AVST_DOWN_META_W))::set(null, "", "vif_avst_down", avst_down);
        uvm_config_db#(virtual avst_if #(CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, CC_MFB_ITEM_WIDTH, AVST_UP_META_W))::set(null, "", "vif_avst_up", avst_up);
        // Credit control interface
        uvm_config_db#(virtual crdt_if)::set(null, "", "vif_crdt_down", crdt_down);
        uvm_config_db#(virtual crdt_if)::set(null, "", "vif_crdt_up", crdt_up);
        // AXI interface
        uvm_config_db#(virtual axi_if #(AXI_DATA_WIDTH, AXI_CQUSER_WIDTH))::set(null, "", "vif_cq_axi", cq_axi);
        uvm_config_db#(virtual axi_if #(AXI_DATA_WIDTH, AXI_CCUSER_WIDTH))::set(null, "", "vif_cc_axi", cc_axi);
        uvm_config_db#(virtual axi_if #(AXI_DATA_WIDTH, AXI_RCUSER_WIDTH))::set(null, "", "vif_rc_axi", rc_axi);
        uvm_config_db#(virtual axi_if #(AXI_DATA_WIDTH, AXI_RQUSER_WIDTH))::set(null, "", "vif_rq_axi", rq_axi);
        // MFB interface
        uvm_config_db#(virtual mfb_if #(RQ_MFB_REGIONS, RQ_MFB_REGION_SIZE, RQ_MFB_BLOCK_SIZE, RQ_MFB_ITEM_WIDTH, RQ_MFB_META_W))::set(null, "", "vif_rq_mfb", rq_mfb);
        uvm_config_db#(virtual mfb_if #(RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, RC_MFB_ITEM_WIDTH, RC_MFB_META_W))::set(null, "", "vif_rc_mfb", rc_mfb);
        uvm_config_db#(virtual mfb_if #(CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, CQ_MFB_ITEM_WIDTH, CQ_MFB_META_W))::set(null, "", "vif_cq_mfb", cq_mfb);
        uvm_config_db#(virtual mfb_if #(CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, CC_MFB_ITEM_WIDTH, CC_MFB_META_W))::set(null, "", "vif_cc_mfb", cc_mfb);

        m_root = uvm_root::get();
        m_root.finish_on_completion = 0;
        m_root.set_report_id_action_hier("ILLEGALNAME",UVM_NO_ACTION);

        uvm_config_db#(int)            ::set(null, "", "recording_detail", 0);
        uvm_config_db#(uvm_bitstream_t)::set(null, "", "recording_detail", 0);

        run_test();
        $stop(2);
    end

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // DUT
    DUT DUT_U (
        .CLK      (CLK),
        .RST      (reset.RESET),
        // For Intel
        .avst_up   (avst_up),
        .avst_down (avst_down),
        // For Credit control
        .crdt_down (crdt_down),
        .crdt_up   (crdt_up),
        // For Xilinx
        .cq_axi    (cq_axi),
        .cc_axi    (cc_axi),
        .rc_axi    (rc_axi),
        .rq_axi    (rq_axi),
        // For MFB
        .rq_mfb    (rq_mfb),
        .rc_mfb    (rc_mfb),
        .cq_mfb    (cq_mfb),
        .cc_mfb    (cc_mfb)
    );

endmodule
