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

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Interfaces
    reset_if  reset(CLK);
    pullup (reset.RESET);

    // For Intel (AVALON)
    localparam AVST_UP_META_W   = 128 + 32 + 1; // HDR + PREFIX + ERROR
    localparam AVST_DOWN_META_W = 128 + 32 + 3; // HDR + PREFIX + BAR_RANGE
    avst_if #(
        .REGIONS     (CQ_MFB_REGIONS),
        .REGION_SIZE (CQ_MFB_REGION_SIZE*CQ_MFB_BLOCK_SIZE),
        .ITEM_WIDTH  (CQ_MFB_ITEM_WIDTH),
        .META_WIDTH  (AVST_DOWN_META_W)
    ) avst_down(CLK);
    avst_if #(
        .REGIONS     (CC_MFB_REGIONS),
        .REGION_SIZE (CC_MFB_REGION_SIZE*CC_MFB_BLOCK_SIZE),
        .ITEM_WIDTH  (CC_MFB_ITEM_WIDTH),
        .META_WIDTH  (AVST_UP_META_W)
    )   avst_up(CLK);
    // For Credit control
    crdt_if crdt_down(CLK);
    crdt_if crdt_up(CLK);
    // For Xilinx (AXI)
    localparam AXI_ITEMS     = CQ_MFB_REGIONS*CQ_MFB_REGION_SIZE*CQ_MFB_BLOCK_SIZE;
    axi_if #(
        .ITEMS       (AXI_ITEMS),
        .ITEM_WIDTH  (CQ_MFB_ITEM_WIDTH),
        .TUSER_WIDTH (uvm_pcie_axi::tuser_width_get(AXI_ITEMS, uvm_pcie_axi::AXI_CQ))
    ) cq_axi(CLK);
    axi_if #(
        .ITEMS       (AXI_ITEMS),
        .ITEM_WIDTH  (CC_MFB_ITEM_WIDTH),
        .TUSER_WIDTH (uvm_pcie_axi::tuser_width_get(AXI_ITEMS, uvm_pcie_axi::AXI_CC))
    ) cc_axi(CLK);
    axi_if #(
        .ITEMS       (AXI_ITEMS),
        .ITEM_WIDTH  (RC_MFB_ITEM_WIDTH),
        .TUSER_WIDTH (uvm_pcie_axi::tuser_width_get(AXI_ITEMS, uvm_pcie_axi::AXI_RC))
    ) rc_axi(CLK);
    axi_if #(
        .ITEMS       (AXI_ITEMS),
        .ITEM_WIDTH  (RQ_MFB_ITEM_WIDTH),
        .TUSER_WIDTH (uvm_pcie_axi::tuser_width_get(AXI_ITEMS, uvm_pcie_axi::AXI_RQ))
    ) rq_axi(CLK);
        // For Intel and Xilinx (MFB)
    mfb_if #(
        .REGIONS     (RQ_MFB_REGIONS),
        .REGION_SIZE (RQ_MFB_REGION_SIZE),
        .BLOCK_SIZE  (RQ_MFB_BLOCK_SIZE),
        .ITEM_WIDTH  (RQ_MFB_ITEM_WIDTH),
        .META_WIDTH  (sv_pcie_meta_pack::PCIE_RQ_META_WIDTH)
    ) rq_mfb(CLK);
    mfb_if #(
        .REGIONS     (RC_MFB_REGIONS),
        .REGION_SIZE (RC_MFB_REGION_SIZE),
        .BLOCK_SIZE  (RC_MFB_BLOCK_SIZE),
        .ITEM_WIDTH  (RC_MFB_ITEM_WIDTH),
        .META_WIDTH  (sv_pcie_meta_pack::PCIE_RC_META_WIDTH)
    ) rc_mfb(CLK);
    mfb_if #(
        .REGIONS     (CQ_MFB_REGIONS),
        .REGION_SIZE (CQ_MFB_REGION_SIZE),
        .BLOCK_SIZE  (CQ_MFB_BLOCK_SIZE),
        .ITEM_WIDTH  (CQ_MFB_ITEM_WIDTH),
        .META_WIDTH  (sv_pcie_meta_pack::PCIE_CQ_META_WIDTH)
    ) cq_mfb(CLK);
    mfb_if #(
        .REGIONS     (CC_MFB_REGIONS),
        .REGION_SIZE (CC_MFB_REGION_SIZE),
        .BLOCK_SIZE  (CC_MFB_BLOCK_SIZE),
        .ITEM_WIDTH  (CC_MFB_ITEM_WIDTH),
        .META_WIDTH  (sv_pcie_meta_pack::PCIE_CC_META_WIDTH)
    ) cc_mfb(CLK);
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
        uvm_config_db#(virtual avst_if #(
            .REGIONS     (CQ_MFB_REGIONS),
            .REGION_SIZE (CQ_MFB_REGION_SIZE*CQ_MFB_BLOCK_SIZE),
            .ITEM_WIDTH  (CQ_MFB_ITEM_WIDTH),
            .META_WIDTH  (AVST_DOWN_META_W)
        ))::set(null, "", "vif_pcie_down_avst", avst_down);
        uvm_config_db#(virtual avst_if #(
            .REGIONS     (CC_MFB_REGIONS),
            .REGION_SIZE (CC_MFB_REGION_SIZE*CC_MFB_BLOCK_SIZE),
            .ITEM_WIDTH  (CC_MFB_ITEM_WIDTH),
            .META_WIDTH  (AVST_UP_META_W)
        ))::set(null, "",   "vif_pcie_up_avst"  , avst_up);
        // Credit control interface
        uvm_config_db#(virtual crdt_if)::set(null, "", "vif_crdt_down", crdt_down);
        uvm_config_db#(virtual crdt_if)::set(null, "", "vif_crdt_up", crdt_up);
        // AXI interface
        uvm_config_db#(virtual axi_if #(
            .ITEMS       (AXI_ITEMS),
            .ITEM_WIDTH  (CQ_MFB_ITEM_WIDTH),
            .TUSER_WIDTH (uvm_pcie_axi::tuser_width_get(AXI_ITEMS, uvm_pcie_axi::AXI_CQ))
        ))::set(null, "", "vif_pcie_cq_axi", cq_axi);
        uvm_config_db#(virtual axi_if #(
            .ITEMS       (AXI_ITEMS),
            .ITEM_WIDTH  (CC_MFB_ITEM_WIDTH),
            .TUSER_WIDTH (uvm_pcie_axi::tuser_width_get(AXI_ITEMS, uvm_pcie_axi::AXI_CC))
        ))::set(null, "", "vif_pcie_cc_axi", cc_axi);
        uvm_config_db#(virtual axi_if #(
            .ITEMS       (AXI_ITEMS),
            .ITEM_WIDTH  (RC_MFB_ITEM_WIDTH),
            .TUSER_WIDTH (uvm_pcie_axi::tuser_width_get(AXI_ITEMS, uvm_pcie_axi::AXI_RC))
        ))::set(null, "", "vif_pcie_rc_axi", rc_axi);
        uvm_config_db#(virtual axi_if #(
            .ITEMS       (AXI_ITEMS),
            .ITEM_WIDTH  (RQ_MFB_ITEM_WIDTH),
            .TUSER_WIDTH (uvm_pcie_axi::tuser_width_get(AXI_ITEMS, uvm_pcie_axi::AXI_RQ))
        ))::set(null, "", "vif_pcie_rq_axi", rq_axi);
        // MFB interface
        uvm_config_db#(virtual mfb_if #(
            .REGIONS     (RQ_MFB_REGIONS),
            .REGION_SIZE (RQ_MFB_REGION_SIZE),
            .BLOCK_SIZE  (RQ_MFB_BLOCK_SIZE),
            .ITEM_WIDTH  (RQ_MFB_ITEM_WIDTH),
            .META_WIDTH  (sv_pcie_meta_pack::PCIE_RQ_META_WIDTH)
        ))::set(null, "", "vif_usr_rq_mfb", rq_mfb);
        uvm_config_db#(virtual mfb_if #(
            .REGIONS     (RC_MFB_REGIONS),
            .REGION_SIZE (RC_MFB_REGION_SIZE),
            .BLOCK_SIZE  (RC_MFB_BLOCK_SIZE),
            .ITEM_WIDTH  (RC_MFB_ITEM_WIDTH),
            .META_WIDTH  (sv_pcie_meta_pack::PCIE_RC_META_WIDTH)
        ))::set(null, "", "vif_usr_rc_mfb", rc_mfb);
        uvm_config_db#(virtual mfb_if #(
            .REGIONS     (CQ_MFB_REGIONS),
            .REGION_SIZE (CQ_MFB_REGION_SIZE),
            .BLOCK_SIZE  (CQ_MFB_BLOCK_SIZE),
            .ITEM_WIDTH  (CQ_MFB_ITEM_WIDTH),
            .META_WIDTH  (sv_pcie_meta_pack::PCIE_CQ_META_WIDTH)
        ))::set(null, "", "vif_usr_cq_mfb", cq_mfb);
        uvm_config_db#(virtual mfb_if #(
            .REGIONS     (CC_MFB_REGIONS),
            .REGION_SIZE (CC_MFB_REGION_SIZE),
            .BLOCK_SIZE  (CC_MFB_BLOCK_SIZE),
            .ITEM_WIDTH  (CC_MFB_ITEM_WIDTH),
            .META_WIDTH  (sv_pcie_meta_pack::PCIE_CC_META_WIDTH)
        ))::set(null, "", "vif_usr_cc_mfb", cc_mfb);

        m_root = uvm_root::get();
        m_root.finish_on_completion = 0;
        m_root.set_report_id_action_hier("ILLEGALNAME",UVM_NO_ACTION);

        uvm_config_db#(int)            ::set(null, "", "recording_detail", 0);
        uvm_config_db#(uvm_bitstream_t)::set(null, "", "recording_detail", 0);

        run_test();
        $stop(2);
    end

    //assign avst_down.VALID = 0;
    //assign avst_up.READY = 0;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // dut
    dut DUT_U (
        .CLK      (CLK),
        .RST      ((reset.RESET == 1'b1) ? 1'b1 : 1'b0),
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


    PROPERTY #(
       .ENDPOINT_TYPE     (ENDPOINT_TYPE),

       .RC_MFB_REGIONS    (RC_MFB_REGIONS    ),
       .RC_MFB_REGION_SIZE(RC_MFB_REGION_SIZE),
       .RC_MFB_BLOCK_SIZE (RC_MFB_BLOCK_SIZE ),
       .RC_MFB_ITEM_WIDTH (RC_MFB_ITEM_WIDTH ),
       .RC_MFB_META_W     (sv_pcie_meta_pack::PCIE_RC_META_WIDTH),

       .CQ_MFB_REGIONS    (CQ_MFB_REGIONS    ),
       .CQ_MFB_REGION_SIZE(CQ_MFB_REGION_SIZE),
       .CQ_MFB_BLOCK_SIZE (CQ_MFB_BLOCK_SIZE ),
       .CQ_MFB_ITEM_WIDTH (CQ_MFB_ITEM_WIDTH ),
       .CQ_MFB_META_W     (sv_pcie_meta_pack::PCIE_CQ_META_WIDTH)
    )
    PROPERTY_U (
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
