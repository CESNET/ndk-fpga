/*
 * dut.sv: design under test.
 * Copyright (C) 2020 CESNET z. s. p. o.
 * Author(s): Radek Iša <isa@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 */

//MTC convert PCIE transaction to MI
import test_pkg::*;

// ----------------------------------------------------------------------------
//                        Module declaration
// ----------------------------------------------------------------------------

module DUT (
	input logic   RESET,
	input logic   CLK,

    i_pcie_c      PCIE_C,
    iMi.slave     MI
);

    /////////////////////////////////////////
    // STRATIX
    localparam AVALON_REGIONS      = 2;
    localparam AVALON_REGION_SIZE  = 1;
    localparam AVALON_BLOCK_SIZE   = 8;
    localparam AVALON_ITEM_WIDTH   = 32;

    logic [AVALON_REGIONS*AVALON_REGION_SIZE*AVALON_BLOCK_SIZE*AVALON_ITEM_WIDTH-1:0] avalon_cc_mfb_data;
    logic [AVALON_REGIONS*(32+128)-1:0] avalon_cc_mfb_meta;
    logic [AVALON_REGIONS-1:0]          avalon_cc_mfb_sof;
    logic [AVALON_REGIONS-1:0]          avalon_cc_mfb_eof;
    logic [AVALON_REGIONS*$clog2(AVALON_REGION_SIZE)-1:0] avalon_cc_mfb_sof_pos;
    logic [AVALON_REGIONS*$clog2(AVALON_REGION_SIZE*AVALON_BLOCK_SIZE)-1:0] avalon_cc_mfb_eof_pos;
    logic avalon_cc_mfb_src_rdy;  //  std_logic;
    logic avalon_cc_mfb_dst_rdy;  //  std_logic;

    logic [AVALON_REGIONS*AVALON_REGION_SIZE*AVALON_BLOCK_SIZE*AVALON_ITEM_WIDTH-1:0] avalon_cq_mfb_data;
    logic [AVALON_REGIONS*(3+32+128)-1:0] avalon_cq_mfb_meta;
    logic [AVALON_REGIONS-1:0] avalon_cq_mfb_sof;
    logic [AVALON_REGIONS-1:0] avalon_cq_mfb_eof;
    logic [AVALON_REGIONS*$clog2(AVALON_REGION_SIZE)-1:0] avalon_cq_mfb_sof_pos;
    logic [AVALON_REGIONS*$clog2(AVALON_REGION_SIZE*AVALON_BLOCK_SIZE)-1:0] avalon_cq_mfb_eof_pos;
    logic avalon_cq_mfb_src_rdy;
    logic avalon_cq_mfb_dst_rdy;

    //////////////////////////////////////////
    // AXI
    //localparam AXI_CQ_TUSER_WIDTH = (DEVICE=="7SERIES") ? 85 : (DEVICE=="ULTRASCALE" && PCIE_DATA_WIDTH == 512) ? 183 : 88;
    //localparam AXI_CC_TUSER_WIDTH = (DEVICE=="7SERIES") ? 33 : (DEVICE=="ULTRASCALE" && PCIE_DATA_WIDTH == 512) ? 81  : 33;
    localparam AXI_CQ_TUSER_WIDTH = (DEVICE=="7SERIES") ? 85 :  183;
    localparam AXI_CC_TUSER_WIDTH = (DEVICE=="7SERIES") ? 33 :  81;

    logic [PCIE_DATA_WIDTH-1:0]    axi_cq_data;
    logic [AXI_CQ_TUSER_WIDTH-1:0] axi_cq_user;
    logic [PCIE_DATA_WIDTH/32-1:0] axi_cq_keep;
    logic axi_cq_last;
    logic axi_cq_valid;
    logic axi_cq_ready;

    logic [PCIE_DATA_WIDTH-1:0]    axi_cc_data;
    logic [AXI_CC_TUSER_WIDTH-1:0] axi_cc_user;
    logic [PCIE_DATA_WIDTH/32-1:0] axi_cc_keep;
    logic axi_cc_last;
    logic axi_cc_valid;
    logic axi_cc_ready;

    if(DEVICE == "ULTRASCALE" || DEVICE == "7SERIES") begin
        assign axi_cq_data  = PCIE_C.AXI.CQ.TDATA;
        assign axi_cq_user  = PCIE_C.AXI.CQ.TUSER;
        assign axi_cq_last  = PCIE_C.AXI.CQ.TLAST;
        assign axi_cq_keep  = PCIE_C.AXI.CQ.TKEEP;
        assign axi_cq_valid = PCIE_C.AXI.CQ.TVALID;
        assign PCIE_C.AXI.CQ.TREADY = axi_cq_ready & (~RESET);

        assign PCIE_C.AXI.CC.TDATA = axi_cc_data;
        assign PCIE_C.AXI.CC.TUSER = axi_cc_user;
        assign PCIE_C.AXI.CC.TLAST = axi_cc_last;
        assign PCIE_C.AXI.CC.TKEEP = axi_cc_keep;
        assign PCIE_C.AXI.CC.TVALID = axi_cc_valid;
        assign axi_cc_ready = PCIE_C.AXI.CC.TREADY;
    end else if (DEVICE == "STRATIX10") begin
        PCIE_CONNECTION_BLOCK #(
            .MFB_REGIONS         (AVALON_REGIONS),
            .MFB_REGION_SIZE     (AVALON_REGION_SIZE),
            .MFB_BLOCK_SIZE      (AVALON_BLOCK_SIZE),
            .MFB_ITEM_WIDTH      (AVALON_ITEM_WIDTH),
            .MFB_UP_META_WIDTH   (32+128),
            .MFB_DOWN_META_WIDTH (3+32+128),
            .DEVICE              (DEVICE),
            .ENDPOINT_TYPE       ("P_TILE")
        )
        CONNECTION_BLOCK (
            //-- =====================================================================
            //-- CLOCK AND RESET
            //-- =====================================================================
            .CLK               (CLK),
            .RESET             (RESET),
            //-- =====================================================================
            //-- TO/FROM STRATIX 10 PCIE H-TILE/P-TILE IP CORE
            //-- =====================================================================
            //-- DOWN stream
            .RX_AVST_DATA      (PCIE_C.AVALON.CQ.data),
            .RX_AVST_HDR       (PCIE_C.AVALON.CQ.hdr),
            .RX_AVST_PREFIX    (PCIE_C.AVALON.CQ.prefix),
            .RX_AVST_SOP       (PCIE_C.AVALON.CQ.sop),
            .RX_AVST_EOP       (PCIE_C.AVALON.CQ.eop),
            .RX_AVST_EMPTY     (PCIE_C.AVALON.CQ.empty),
            .RX_AVST_BAR_RANGE (PCIE_C.AVALON.CQ.bar_range), //: in  std_logic_vector(
            .RX_AVST_VALID     (PCIE_C.AVALON.CQ.valid),
            .RX_AVST_READY     (PCIE_C.AVALON.CQ.ready),
            //-- UP stream
            .TX_AVST_DATA      (PCIE_C.AVALON.CC.data),
            .TX_AVST_HDR       (PCIE_C.AVALON.CC.hdr),
            .TX_AVST_PREFIX    (PCIE_C.AVALON.CC.prefix),
            .TX_AVST_SOP       (PCIE_C.AVALON.CC.sop),
            .TX_AVST_EOP       (PCIE_C.AVALON.CC.eop),
            .TX_AVST_ERROR     (PCIE_C.AVALON.CC.error),
            .TX_AVST_VALID     (PCIE_C.AVALON.CC.valid),
            .TX_AVST_READY     (PCIE_C.AVALON.CC.ready),
            // DOWN stream credits - R-TILE only
            .CRDT_DOWN_INIT_DONE(),
            .CRDT_DOWN_UPDATE(),
            .CRDT_DOWN_CNT_PH(),
            .CRDT_DOWN_CNT_NPH(),
            .CRDT_DOWN_CNT_CPLH(),
            .CRDT_DOWN_CNT_PD(),
            .CRDT_DOWN_CNT_NPD(),
            .CRDT_DOWN_CNT_CPLD(),

            // UP stream credits - R-TILE only
            .CRDT_UP_INIT_DONE(),
            .CRDT_UP_UPDATE(),
            .CRDT_UP_CNT_PH(),
            .CRDT_UP_CNT_NPH(),
            .CRDT_UP_CNT_CPLH(),
            .CRDT_UP_CNT_PD(),
            .CRDT_UP_CNT_NPD(),
            .CRDT_UP_CNT_CPLD(),


            //-- =====================================================================
            //-- TO/FROM PCIE TRANSACTION CONTROLER (PTC)
            //-- =====================================================================
            //-- UP stream
            .RQ_MFB_DATA       (),
            .RQ_MFB_META       (),
            .RQ_MFB_SOF        (),
            .RQ_MFB_EOF        (),
            .RQ_MFB_SOF_POS    (),
            .RQ_MFB_EOF_POS    (),
            .RQ_MFB_SRC_RDY    (1'b0),
            .RQ_MFB_DST_RDY    (),
            //.-- DOWN stream
            .RC_MFB_DATA       (),
            .RC_MFB_META       (),
            .RC_MFB_SOF        (),
            .RC_MFB_EOF        (),
            .RC_MFB_SOF_POS    (),
            .RC_MFB_EOF_POS    (),
            .RC_MFB_SRC_RDY    (),
            .RC_MFB_DST_RDY    (1'b1),

            //.-- =====================================================================
            //.-- TO/FROM MI32 TRANSACTION CONTROLER (MTC)
            //.-- =====================================================================
            //.-- UP stream
            .CC_MFB_DATA       (avalon_cc_mfb_data   ),
            .CC_MFB_META       (avalon_cc_mfb_meta   ),
            .CC_MFB_SOF        (avalon_cc_mfb_sof    ),
            .CC_MFB_EOF        (avalon_cc_mfb_eof    ),
            .CC_MFB_SOF_POS    (avalon_cc_mfb_sof_pos),
            .CC_MFB_EOF_POS    (avalon_cc_mfb_eof_pos),
            .CC_MFB_SRC_RDY    (avalon_cc_mfb_src_rdy),
            .CC_MFB_DST_RDY    (avalon_cc_mfb_dst_rdy),
            //.-- DOWN stream
            .CQ_MFB_DATA       (avalon_cq_mfb_data   ),
            .CQ_MFB_META       (avalon_cq_mfb_meta   ),
            .CQ_MFB_SOF        (avalon_cq_mfb_sof    ),
            .CQ_MFB_EOF        (avalon_cq_mfb_eof    ),
            .CQ_MFB_SOF_POS    (avalon_cq_mfb_sof_pos),
            .CQ_MFB_EOF_POS    (avalon_cq_mfb_eof_pos),
            .CQ_MFB_SRC_RDY    (avalon_cq_mfb_src_rdy),
            .CQ_MFB_DST_RDY    (avalon_cq_mfb_dst_rdy)
        );
    end

    ///////////////////////////////////////////////////////////
    // MTC
    ///////////////////////////////////////////////////////////
	logic cq_np_req;
	logic mi_function[8];

    MTC_WRAPPER #(
    	.AXI_DATA_WIDTH         (PCIE_DATA_WIDTH),
    	.AXI_CQUSER_WIDTH       (AXI_CQ_TUSER_WIDTH),
    	.AXI_CCUSER_WIDTH       (AXI_CC_TUSER_WIDTH),
    	.BAR0_BASE_ADDR         (32'h0),
        .MFB_REGIONS            (AVALON_REGIONS),
        .MFB_REGION_SIZE        (AVALON_REGION_SIZE),
        .MFB_BLOCK_SIZE         (AVALON_BLOCK_SIZE),
        .MFB_ITEM_WIDTH         (AVALON_ITEM_WIDTH),
        .MFB_CQ_META_WIDTH      (3+32+128),
        .MFB_CC_META_WIDTH      (32+128),
        .DEVICE                 (DEVICE),
        .ENDPOINT_TYPE          ("P_TILE")
    )
    DUT_U (
        .CLK    (CLK),
        .RESET  (RESET),

        //-- =====================================================================
        //--  Configuration Status Interface
        //-- =====================================================================
        //-- Maximum allowed size of completion payload
    	.CTL_MAX_PAYLOAD_SIZE   (3'b0),
        //-- BAR aperture value (Intel only)
        .CTL_BAR_APERTURE       (6'd24),

    	.CQ_AXI_DATA            (axi_cq_data),
    	.CQ_AXI_USER            (axi_cq_user),
    	.CQ_AXI_KEEP            (axi_cq_keep),
    	.CQ_AXI_LAST            (axi_cq_last),
    	.CQ_AXI_VALID           (axi_cq_valid),
    	.CQ_AXI_READY           (axi_cq_ready),

    	.CC_AXI_DATA            (axi_cc_data),
    	.CC_AXI_USER            (axi_cc_user),
    	.CC_AXI_KEEP            (axi_cc_keep),
    	.CC_AXI_LAST            (axi_cc_last),
    	.CC_AXI_VALID           (axi_cc_valid),
    	.CC_AXI_READY           (axi_cc_ready),

        //-- =====================================================================
        //--  MFB Completer Request Interface (CQ) - Intel Only
        //-- =====================================================================
        .CQ_MFB_DATA       (avalon_cq_mfb_data   ),
        .CQ_MFB_META       (avalon_cq_mfb_meta   ),
        .CQ_MFB_SOF        (avalon_cq_mfb_sof    ),
        .CQ_MFB_EOF        (avalon_cq_mfb_eof    ),
        .CQ_MFB_SOF_POS    (avalon_cq_mfb_sof_pos),
        .CQ_MFB_EOF_POS    (avalon_cq_mfb_eof_pos),
        .CQ_MFB_SRC_RDY    (avalon_cq_mfb_src_rdy),
        .CQ_MFB_DST_RDY    (avalon_cq_mfb_dst_rdy),

        //-- =====================================================================
        //--  MFB Completer Completion Interface (CC) - Intel Only
        //-- =====================================================================
        .CC_MFB_DATA       (avalon_cc_mfb_data   ),
        .CC_MFB_META       (avalon_cc_mfb_meta   ),
        .CC_MFB_SOF        (avalon_cc_mfb_sof    ),
        .CC_MFB_EOF        (avalon_cc_mfb_eof    ),
        .CC_MFB_SOF_POS    (avalon_cc_mfb_sof_pos),
        .CC_MFB_EOF_POS    (avalon_cc_mfb_eof_pos),
        .CC_MFB_SRC_RDY    (avalon_cc_mfb_src_rdy),
        .CC_MFB_DST_RDY    (avalon_cc_mfb_dst_rdy),

        //-- =====================================================================
        //--  MI32 interface (master)
        //-- =====================================================================
    	.MI_FUNCTION            (mi_function),
    	.MI_DWR                 (MI.DWR),
    	.MI_ADDR                (MI.ADDR),
    	.MI_BE                  (MI.BE),
    	.MI_RD                  (MI.RD),
    	.MI_WR                  (MI.WR),
    	.MI_DRDY                (MI.DRDY),
    	.MI_ARDY                (MI.ARDY),
    	.MI_DRD                 (MI.DRD)
    );

endmodule
