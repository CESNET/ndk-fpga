//-- dut.sv: Design under test 
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import test::*;

module DUT (
    input logic CLK,
    input logic RST,
    // For Intel
    avst_if.dut_rx avst_down,
    avst_if.dut_tx avst_up,
    // Credit control
    crdt_if.dut_tx crdt_down,
    crdt_if.dut_rx crdt_up,
    // For Xilinx
    axi_if.dut_rx cq_axi,
    axi_if.dut_tx cc_axi,
    axi_if.dut_rx rc_axi,
    axi_if.dut_tx rq_axi,
    // For Intel and Xilinx
    mfb_if.dut_rx rq_mfb,
    mfb_if.dut_tx rc_mfb,
    mfb_if.dut_tx cq_mfb,
    mfb_if.dut_rx cc_mfb
    );

    localparam RC_SOF_POS_WIDTH   = ((RC_MFB_REGION_SIZE*RC_MFB_REGIONS) == RC_MFB_REGIONS) ? RC_MFB_REGIONS : (RC_MFB_REGIONS*$clog2(RC_MFB_REGION_SIZE));
    localparam CC_SOF_POS_WIDTH   = ((CC_MFB_REGION_SIZE*CC_MFB_REGIONS) == CC_MFB_REGIONS) ? CC_MFB_REGIONS : (CC_MFB_REGIONS*$clog2(CC_MFB_REGION_SIZE));
    localparam RQ_SOF_POS_WIDTH   = ((RQ_MFB_REGION_SIZE*RQ_MFB_REGIONS) == RQ_MFB_REGIONS) ? RQ_MFB_REGIONS : (RQ_MFB_REGIONS*$clog2(RQ_MFB_REGION_SIZE));
    localparam CQ_SOF_POS_WIDTH   = ((CQ_MFB_REGION_SIZE*CQ_MFB_REGIONS) == CQ_MFB_REGIONS) ? CQ_MFB_REGIONS : (CQ_MFB_REGIONS*$clog2(CQ_MFB_REGION_SIZE));
    localparam HDR_WIDTH       = 128;
    localparam PREFIX_WIDTH    = 32;
    localparam BAR_RANGE_WIDTH = 3;

    logic [RC_SOF_POS_WIDTH-1 : 0]   rc_sof_pos    ;
    logic [CC_SOF_POS_WIDTH-1 : 0]   cc_sof_pos    ;
    logic [RQ_SOF_POS_WIDTH-1 : 0]   rq_sof_pos    ;
    logic [CQ_SOF_POS_WIDTH-1 : 0]   cq_sof_pos    ;
    logic [CQ_MFB_REGIONS*128-1 : 0] down_hdr      ;
    logic [CQ_MFB_REGIONS*32-1  : 0] down_prefix   ;
    logic [CQ_MFB_REGIONS*3-1   : 0] down_bar_range;

    logic [CC_MFB_REGIONS*128-1 : 0] up_hdr;
    logic [CC_MFB_REGIONS*32-1  : 0] up_prefix;
    logic [CC_MFB_REGIONS-1     : 0] up_error;

    generate
        for (genvar r = 0; r < CQ_MFB_REGIONS; r++) begin
            assign down_bar_range [(r+1)*BAR_RANGE_WIDTH-1 : r*BAR_RANGE_WIDTH] = avst_down.META[(r+1)*(AVST_DOWN_META_W)-1                                : (r+1)*AVST_DOWN_META_W - BAR_RANGE_WIDTH];
            assign down_prefix    [(r+1)*PREFIX_WIDTH-1    : r*PREFIX_WIDTH]    = avst_down.META[(r+1)*AVST_DOWN_META_W - BAR_RANGE_WIDTH-1                : (r+1)*AVST_DOWN_META_W - PREFIX_WIDTH - BAR_RANGE_WIDTH];
            assign down_hdr       [(r+1)*HDR_WIDTH-1       : r*HDR_WIDTH]       = avst_down.META[(r+1)*AVST_DOWN_META_W - PREFIX_WIDTH - BAR_RANGE_WIDTH-1 : (r+1)*AVST_DOWN_META_W - HDR_WIDTH - PREFIX_WIDTH - BAR_RANGE_WIDTH];
        end

        for (genvar r = 0; r < CC_MFB_REGIONS; r++) begin
            assign avst_up.META[(r+1)*(AVST_UP_META_W)-1                  : (r+1)*AVST_UP_META_W - 1]                            = up_error  [r];
            assign avst_up.META[(r+1)*AVST_UP_META_W - 1-1                : (r+1)*AVST_UP_META_W - PREFIX_WIDTH - 1]             = up_prefix [(r+1)*PREFIX_WIDTH-1    : r*PREFIX_WIDTH];
            assign avst_up.META[(r+1)*AVST_UP_META_W - PREFIX_WIDTH - 1-1 : (r+1)*AVST_UP_META_W - HDR_WIDTH - PREFIX_WIDTH - 1] = up_hdr    [(r+1)*HDR_WIDTH-1       : r*HDR_WIDTH];
        end
    endgenerate

    assign rc_mfb.SOF_POS = rc_sof_pos;
    assign rq_sof_pos     = rq_mfb.SOF_POS;
    assign cq_mfb.SOF_POS = cq_sof_pos;
    assign cc_sof_pos     = cc_mfb.SOF_POS;
    assign avst_up.EMPTY  = '0;

    PCIE_ADAPTER #(
        // =====================================================================
        // MFB configuration
        // =====================================================================
        // CQ MFB
        .CQ_MFB_REGIONS     (CQ_MFB_REGIONS),
        .CQ_MFB_REGION_SIZE (CQ_MFB_REGION_SIZE),
        .CQ_MFB_BLOCK_SIZE  (CQ_MFB_BLOCK_SIZE),
        .CQ_MFB_ITEM_WIDTH  (CQ_MFB_ITEM_WIDTH),
        // RC MFB
        .RC_MFB_REGIONS     (RC_MFB_REGIONS),
        .RC_MFB_REGION_SIZE (RC_MFB_REGION_SIZE),
        .RC_MFB_BLOCK_SIZE  (RC_MFB_BLOCK_SIZE),
        .RC_MFB_ITEM_WIDTH  (RC_MFB_ITEM_WIDTH),
        // CC MFB
        .CC_MFB_REGIONS     (CC_MFB_REGIONS),
        .CC_MFB_REGION_SIZE (CC_MFB_REGION_SIZE),
        .CC_MFB_BLOCK_SIZE  (CC_MFB_BLOCK_SIZE),
        .CC_MFB_ITEM_WIDTH  (CC_MFB_ITEM_WIDTH),
        // RQ MFB
        .RQ_MFB_REGIONS     (RQ_MFB_REGIONS),
        .RQ_MFB_REGION_SIZE (RQ_MFB_REGION_SIZE),
        .RQ_MFB_BLOCK_SIZE  (RQ_MFB_BLOCK_SIZE),
        .RQ_MFB_ITEM_WIDTH  (RQ_MFB_ITEM_WIDTH),

        // =====================================================================
        // Common configuration
        // =====================================================================
        // Connected PCIe endpoint type
        .ENDPOINT_TYPE      (ENDPOINT_TYPE),
        // FPGA device
        .DEVICE             (DEVICE),
        // Depth of CQ FIFO (R-Tile only)
        .CQ_FIFO_ITEMS      (CQ_FIFO_ITEMS),
        // Maximum write request (payload) size (in DWORDs)
        .PCIE_MPS_DW        (PCIE_MPS_DW),

        // =====================================================================
        // AXI configuration
        // =====================================================================

        .AXI_DATA_WIDTH     (CQ_MFB_REGIONS*CQ_MFB_REGION_SIZE*CQ_MFB_BLOCK_SIZE*CQ_MFB_ITEM_WIDTH),
        // Allowed values: 183 (USP Gen3x16), 88 (USP Gen3x8), 85 (V7 Gen3x8)
        .AXI_CQUSER_WIDTH   (AXI_CQUSER_WIDTH),
        // Allowed values: 81 (USP Gen3x16), 33 (USP Gen3x8), 33 (V7 Gen3x8)
        .AXI_CCUSER_WIDTH   (AXI_CCUSER_WIDTH),
        // Allowed values: 137 (USP Gen3x16), 62 (USP Gen3x8), 60 (V7 Gen3x8)
        .AXI_RQUSER_WIDTH   (AXI_RQUSER_WIDTH),
        // Allowed values: 161 (USP Gen3x16), 75 (USP Gen3x8), 75 (V7 Gen3x8)
        .AXI_RCUSER_WIDTH   (AXI_RCUSER_WIDTH),
        .AXI_STRADDLING     (AXI_STRADDLING),

        // =====================================================================
        // AVST configuration (set automatically)
        // =====================================================================

        .AVST_DOWN_SEG      (CQ_MFB_REGIONS),
        .AVST_UP_SEG        (CC_MFB_REGIONS) 
    ) VHDL_DUT_U (
        .PCIE_CLK            (CLK),
        .PCIE_RESET          (RST),

        // =====================================================================
        // Avalon-ST DOWN (CQ+RC) Interface - Intel FPGA Only
        // =====================================================================
        .AVST_DOWN_DATA      (avst_down.DATA),
        .AVST_DOWN_HDR       (down_hdr),
        .AVST_DOWN_PREFIX    (down_prefix),
        .AVST_DOWN_SOP       (avst_down.SOP),
        .AVST_DOWN_EOP       (avst_down.EOP),
        .AVST_DOWN_EMPTY     (avst_down.EMPTY),
        .AVST_DOWN_BAR_RANGE (down_bar_range),
        .AVST_DOWN_VALID     (avst_down.VALID),
        .AVST_DOWN_READY     (avst_down.READY),

        // =====================================================================
        // Avalon-ST UP (CC+RQ) Interface - Intel FPGA Only
        // =====================================================================
        .AVST_UP_DATA        (avst_up.DATA),
        .AVST_UP_HDR         (up_hdr),
        .AVST_UP_PREFIX      (up_prefix),
        .AVST_UP_SOP         (avst_up.SOP),
        .AVST_UP_EOP         (avst_up.EOP),
        .AVST_UP_ERROR       (up_error),
        .AVST_UP_VALID       (avst_up.VALID),
        .AVST_UP_READY       (avst_up.READY),

        // =====================================================================
        // CREDIT FLOW CONTROL UP INTERFACE - Intel R-Tile Only
        // =====================================================================
        .CRDT_DOWN_INIT_DONE (crdt_down.INIT_DONE),
        // Update valid flags vector (from MSB to LSB(),
        .CRDT_DOWN_UPDATE    (crdt_down.UPDATE),
        // Update count of PH credits
        .CRDT_DOWN_CNT_PH    (crdt_down.CNT_PH),
        // Update count of NPH credits
        .CRDT_DOWN_CNT_NPH   (crdt_down.CNT_NPH),
        // Update count of CPLH credits
        .CRDT_DOWN_CNT_CPLH  (crdt_down.CNT_CPLH),
        // Update count of PD credits
        .CRDT_DOWN_CNT_PD    (crdt_down.CNT_PD),
        // Update count of NPD credits
        .CRDT_DOWN_CNT_NPD   (crdt_down.CNT_NPD),
        // Update count of CPLD credits
        .CRDT_DOWN_CNT_CPLD  (crdt_down.CNT_CPLD),

        // =====================================================================
        // CREDIT FLOW CONTROL DOWN INTERFACE - Intel R-Tile Only
        // =====================================================================
        // In init phase must the receiver must set the total number of credits
        // using incremental credit updates. The user logic only receives the
        // credit updates and waits for CRDT_UP_INIT_DONE to be high.
        .CRDT_UP_INIT_DONE   (crdt_up.INIT_DONE),
        // Update valid flags vector (from MSB to LSB(),
        .CRDT_UP_UPDATE      (crdt_up.UPDATE),
        // Update count of PH credits
        .CRDT_UP_CNT_PH      (crdt_up.CNT_PH),
        // Update count of NPH credits
        .CRDT_UP_CNT_NPH     (crdt_up.CNT_NPH),
        // Update count of CPLH credits
        .CRDT_UP_CNT_CPLH    (crdt_up.CNT_CPLH),
        // Update count of PD credits
        .CRDT_UP_CNT_PD      (crdt_up.CNT_PD),
        // Update count of NPD credits
        .CRDT_UP_CNT_NPD     (crdt_up.CNT_NPD),
        // Update count of CPLD credits
        .CRDT_UP_CNT_CPLD    (crdt_up.CNT_CPLD),

        // =====================================================================
        // AXI Completer Request (CQ) Interface - Xilinx FPGA Only
        //
        // See Xilinx PG213 (UltraScale+ Devices Integrated Block for PCI Express).
        // =====================================================================
        .CQ_AXI_DATA       (cq_axi.TDATA),
        .CQ_AXI_USER       (cq_axi.TUSER),
        .CQ_AXI_LAST       (cq_axi.TLAST),
        .CQ_AXI_KEEP       (cq_axi.TKEEP),
        .CQ_AXI_VALID      (cq_axi.TVALID),
        .CQ_AXI_READY      (cq_axi.TREADY),

        // =====================================================================
        // AXI Requester Completion (RC) Interface - Xilinx FPGA Only
        //
        // See Xilinx PG213 (UltraScale+ Devices Integrated Block for PCI Express).
        // =====================================================================
        .RC_AXI_DATA       (rc_axi.TDATA),
        .RC_AXI_USER       (rc_axi.TUSER),
        .RC_AXI_LAST       (rc_axi.TLAST),
        .RC_AXI_KEEP       (rc_axi.TKEEP),
        .RC_AXI_VALID      (rc_axi.TVALID),
        .RC_AXI_READY      (rc_axi.TREADY),

        // =====================================================================
        // AXI Completer Completion (CC) Interface - Xilinx FPGA Only
        //
        // See Xilinx PG213 (UltraScale+ Devices Integrated Block for PCI Express).
        // =====================================================================
        .CC_AXI_DATA       (cc_axi.TDATA),
        .CC_AXI_USER       (cc_axi.TUSER),
        .CC_AXI_LAST       (cc_axi.TLAST),
        .CC_AXI_KEEP       (cc_axi.TKEEP),
        .CC_AXI_VALID      (cc_axi.TVALID),
        .CC_AXI_READY      (cc_axi.TREADY),

        // =====================================================================
        // AXI Requester Request (RQ) Interface - Xilinx FPGA Only
        // 
        // See Xilinx PG213 (UltraScale+ Devices Integrated Block for PCI Express).
        // =====================================================================
        .RQ_AXI_DATA       (rq_axi.TDATA),
        .RQ_AXI_USER       (rq_axi.TUSER),
        .RQ_AXI_LAST       (rq_axi.TLAST),
        .RQ_AXI_KEEP       (rq_axi.TKEEP),
        .RQ_AXI_VALID      (rq_axi.TVALID),
        .RQ_AXI_READY      (rq_axi.TREADY),

        // =====================================================================
        // RQ MFB interface
        //
        // MFB bus for transferring PCIe transactions (format according to the
        // PCIe IP used). Compared to the standard MFB specification, it does
        // not allow gaps (SRC_RDY=0) inside transactions and requires that
        // the first transaction in a word starts at byte 0.
        // =====================================================================
        .RQ_MFB_DATA       (rq_mfb.DATA),
        .RQ_MFB_META       (rq_mfb.META),
        .RQ_MFB_SOF        (rq_mfb.SOF),
        .RQ_MFB_EOF        (rq_mfb.EOF),
        .RQ_MFB_SOF_POS    (rq_sof_pos),
        .RQ_MFB_EOF_POS    (rq_mfb.EOF_POS),
        .RQ_MFB_SRC_RDY    (rq_mfb.SRC_RDY),
        .RQ_MFB_DST_RDY    (rq_mfb.DST_RDY),

        // =====================================================================
        // RC MFB interface
        //
        // MFB bus for transferring PCIe transactions (format according to the
        // PCIe IP used). Compared to the standard MFB specification, it does
        // not allow gaps (SRC_RDY=0) inside transactions and requires that
        // the first transaction in a word starts at byte 0.
        // =====================================================================
        .RC_MFB_DATA       (rc_mfb.DATA),
        .RC_MFB_META       (rc_mfb.META),
        .RC_MFB_SOF        (rc_mfb.SOF),
        .RC_MFB_EOF        (rc_mfb.EOF),
        .RC_MFB_SOF_POS    (rc_sof_pos),
        .RC_MFB_EOF_POS    (rc_mfb.EOF_POS),
        .RC_MFB_SRC_RDY    (rc_mfb.SRC_RDY),
        .RC_MFB_DST_RDY    (rc_mfb.DST_RDY),

        // =====================================================================
        // CQ MFB interface
        //
        // MFB bus for transferring PCIe transactions (format according to the
        // PCIe IP used). Compared to the standard MFB specification, it does
        // not allow gaps (SRC_RDY=0) inside transactions and requires that
        // the first transaction in a word starts at byte 0.
        // =====================================================================
        .CQ_MFB_DATA       (cq_mfb.DATA),
        .CQ_MFB_META       (cq_mfb.META),
        .CQ_MFB_SOF        (cq_mfb.SOF),
        .CQ_MFB_EOF        (cq_mfb.EOF),
        .CQ_MFB_SOF_POS    (cq_sof_pos),
        .CQ_MFB_EOF_POS    (cq_mfb.EOF_POS),
        .CQ_MFB_SRC_RDY    (cq_mfb.SRC_RDY),
        .CQ_MFB_DST_RDY    (cq_mfb.DST_RDY),

        // =====================================================================
        // CC MFB interface
        //
        // MFB bus for transferring PCIe transactions (format according to the
        // PCIe IP used). Compared to the standard MFB specification, it does
        // not allow gaps (SRC_RDY=0) inside transactions and requires that
        // the first transaction in a word starts at byte 0.
        // =====================================================================
        .CC_MFB_DATA       (cc_mfb.DATA),
        .CC_MFB_META       (cc_mfb.META),
        .CC_MFB_SOF        (cc_mfb.SOF),
        .CC_MFB_EOF        (cc_mfb.EOF),
        .CC_MFB_SOF_POS    (cc_sof_pos),
        .CC_MFB_EOF_POS    (cc_mfb.EOF_POS),
        .CC_MFB_SRC_RDY    (cc_mfb.SRC_RDY),
        .CC_MFB_DST_RDY    (cc_mfb.DST_RDY)

    );


endmodule
