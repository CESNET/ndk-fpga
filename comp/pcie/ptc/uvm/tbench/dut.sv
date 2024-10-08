//-- dut.sv: Design under test
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import test::*;

module DUT (
    input logic     CLK    ,
    input logic     CLK_DMA,
    input logic     RST    ,
    input logic     RST_DMA,
    // UPSTREAM
    mfb_if.dut_rx   UP_MFB[DMA_PORTS]  ,
    mvb_if.dut_rx   UP_MVB[DMA_PORTS]  ,
    mfb_if.dut_tx   RQ_MFB             ,
    mvb_if.dut_tx   RQ_MVB             ,
    mvb_if.dut_tx   RQ_PREFIX_MVB      ,
    //reset_if.dut    RST             //,
    // DOWNSTREAM
    mfb_if.dut_rx   RC_MFB             ,
    mvb_if.dut_rx   RC_PREFIX_MVB      ,
    mfb_if.dut_tx   DOWN_MFB[DMA_PORTS],
    mvb_if.dut_tx   DOWN_MVB[DMA_PORTS],
    // AXI
    axi_if.dut_tx   AXI_RQ,
    axi_if.dut_rx   AXI_RC
    );


    localparam DOWN_SOF_POS_WIDTH = (($clog2(MFB_DOWN_REG_SIZE)*DMA_MFB_DOWN_REGIONS) == 0) ? (DMA_MFB_DOWN_REGIONS) : (DMA_MFB_DOWN_REGIONS*$clog2(MFB_DOWN_REG_SIZE));
    localparam DOWN_EOF_POS_WIDTH = DMA_MFB_DOWN_REGIONS*$clog2(MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE);
    localparam UP_SOF_POS_WIDTH = (($clog2(MFB_UP_REG_SIZE)*DMA_MFB_UP_REGIONS) == 0) ? (DMA_MFB_UP_REGIONS) : (DMA_MFB_UP_REGIONS*$clog2(MFB_UP_REG_SIZE));
    localparam UP_EOF_POS_WIDTH   = DMA_MFB_UP_REGIONS*$clog2(MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE);
    localparam RQ_SOF_POS_WIDTH = (($clog2(MFB_UP_REG_SIZE)*MFB_UP_REGIONS) == 0) ? (MFB_UP_REGIONS) : (MFB_UP_REGIONS*$clog2(MFB_UP_REG_SIZE));
    localparam RC_SOF_POS_WIDTH = (($clog2(MFB_DOWN_REG_SIZE)*MFB_DOWN_REGIONS) == 0) ? (MFB_DOWN_REGIONS) : (MFB_DOWN_REGIONS*$clog2(MFB_DOWN_REG_SIZE));

    logic [DMA_MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE*MFB_DOWN_ITEM_WIDTH -1:0]  down_mfb_data     [DMA_PORTS-1:0];
    logic [DMA_MFB_DOWN_REGIONS -1:0]                                                            down_mfb_sof      [DMA_PORTS-1:0];
    logic [DMA_MFB_DOWN_REGIONS -1:0]                                                            down_mfb_eof      [DMA_PORTS-1:0];
    logic [DOWN_SOF_POS_WIDTH -1:0]                                                              down_mfb_sof_pos  [DMA_PORTS-1:0];
    logic [DOWN_EOF_POS_WIDTH -1:0]                                                              down_mfb_eof_pos  [DMA_PORTS-1:0];
    logic [DMA_PORTS-1:0]                                                                        down_mfb_src_rdy;
    logic [DMA_PORTS-1:0]                                                                        down_mfb_dst_rdy;

    logic [DMA_MFB_UP_REGIONS*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE*MFB_UP_ITEM_WIDTH -1:0]          up_mfb_data     [DMA_PORTS-1:0];
    logic [DMA_MFB_UP_REGIONS -1:0]                                                              up_mfb_sof      [DMA_PORTS-1:0];
    logic [DMA_MFB_UP_REGIONS -1:0]                                                              up_mfb_eof      [DMA_PORTS-1:0];
    logic [UP_SOF_POS_WIDTH -1:0]                                                                up_mfb_sof_pos  [DMA_PORTS-1:0];
    logic [UP_EOF_POS_WIDTH -1:0]                                                                up_mfb_eof_pos  [DMA_PORTS-1:0];
    logic [DMA_PORTS-1:0]                                                                        up_mfb_src_rdy;
    logic [DMA_PORTS-1:0]                                                                        up_mfb_dst_rdy;

    logic [DMA_PORTS-1:0]                                                                        up_mvb_src_rdy;
    logic [DMA_PORTS-1:0]                                                                        up_mvb_dst_rdy;
    logic [DMA_MVB_UP_ITEMS*sv_dma_bus_pack::DMA_UPHDR_WIDTH-1 : 0]                              up_mvb_data     [DMA_PORTS-1:0];
    logic [DMA_MVB_UP_ITEMS-1 : 0]                                                               up_mvb_vld      [DMA_PORTS-1:0];

    logic [DMA_PORTS-1:0]                                                                        down_mvb_src_rdy;
    logic [DMA_PORTS-1:0]                                                                        down_mvb_dst_rdy;
    logic [DMA_MVB_DOWN_ITEMS*sv_dma_bus_pack::DMA_DOWNHDR_WIDTH-1 : 0]                          down_mvb_data     [DMA_PORTS-1:0];
    logic [DMA_MVB_DOWN_ITEMS-1 : 0]                                                             down_mvb_vld      [DMA_PORTS-1:0];

    logic [RQ_SOF_POS_WIDTH -1:0]                                                                rq_mfb_sof_pos;
    logic [RC_SOF_POS_WIDTH -1:0]                                                                rc_mfb_sof_pos;

    generate
        for (genvar i = 0; i < DMA_PORTS; i++) begin
            assign DOWN_MFB[i].DATA    = down_mfb_data[i];
            assign DOWN_MFB[i].SOF     = down_mfb_sof[i];
            assign DOWN_MFB[i].EOF     = down_mfb_eof[i];
            assign DOWN_MFB[i].SOF_POS = down_mfb_sof_pos[i];
            assign DOWN_MFB[i].EOF_POS = down_mfb_eof_pos[i];
            assign DOWN_MFB[i].SRC_RDY = down_mfb_src_rdy[i];
            assign down_mfb_dst_rdy[i] = DOWN_MFB[i].DST_RDY;

            assign up_mfb_data[i]      = UP_MFB[i].DATA;
            assign up_mfb_sof[i]       = UP_MFB[i].SOF;
            assign up_mfb_eof[i]       = UP_MFB[i].EOF;

            if ((DMA_MFB_UP_REGIONS*$clog2(MFB_UP_REG_SIZE)) == 0) begin
                assign up_mfb_sof_pos[i] = '0;
            end else
                assign up_mfb_sof_pos[i]   = UP_MFB[i].SOF_POS;

            assign up_mfb_eof_pos[i]   = UP_MFB[i].EOF_POS;
            assign up_mfb_src_rdy[i]   = UP_MFB[i].SRC_RDY;
            assign UP_MFB[i].DST_RDY   = up_mfb_dst_rdy[i];

            assign up_mvb_data   [i]   = UP_MVB[i].DATA;
            assign up_mvb_vld    [i]   = UP_MVB[i].VLD;
            assign up_mvb_src_rdy[i]   = UP_MVB[i].SRC_RDY;
            assign UP_MVB[i].DST_RDY   = up_mvb_dst_rdy[i];

            assign DOWN_MVB[i].DATA    = down_mvb_data[i];
            assign DOWN_MVB[i].VLD     = down_mvb_vld[i];
            assign DOWN_MVB[i].SRC_RDY = down_mvb_src_rdy[i];
            assign down_mvb_dst_rdy[i] = DOWN_MVB[i].DST_RDY;

        end
    endgenerate

    if (DEVICE == "STRATIX10" || DEVICE == "AGILEX") begin
        assign RQ_MVB.SRC_RDY      = RQ_MFB.SRC_RDY;
        assign RQ_MVB.DST_RDY      = RQ_MFB.DST_RDY;
    end else begin
        assign RQ_MVB.SRC_RDY      = AXI_RQ.TVALID;
        assign RQ_MVB.DST_RDY      = AXI_RQ.TREADY;
    end
    assign RQ_MFB.SOF_POS      = rq_mfb_sof_pos;

    if ((DMA_MFB_DOWN_REGIONS*$clog2(MFB_DOWN_REG_SIZE)) == 0) begin
        assign rc_mfb_sof_pos = '0;
    end else
        assign rc_mfb_sof_pos = RC_MFB.SOF_POS;

    PCIE_TRANSACTION_CTRL_WRAPPER #(
        .DMA_PORTS            (DMA_PORTS)           ,
        .MVB_UP_ITEMS         (MVB_UP_ITEMS)        ,
        .DMA_MVB_UP_ITEMS     (DMA_MVB_UP_ITEMS)    ,
        .MFB_UP_REGIONS       (MFB_UP_REGIONS)      ,
        .MFB_UP_REG_SIZE      (MFB_UP_REG_SIZE)     ,
        .MFB_UP_BLOCK_SIZE    (MFB_UP_BLOCK_SIZE)   ,
        .MFB_UP_ITEM_WIDTH    (MFB_UP_ITEM_WIDTH)   ,
        .DMA_MFB_UP_REGIONS   (DMA_MFB_UP_REGIONS)  ,
        .MVB_DOWN_ITEMS       (MVB_DOWN_ITEMS)      ,
        .DMA_MVB_DOWN_ITEMS   (DMA_MVB_DOWN_ITEMS)  ,
        .MFB_DOWN_REGIONS     (MFB_DOWN_REGIONS)    ,
        .MFB_DOWN_REG_SIZE    (MFB_DOWN_REG_SIZE)   ,
        .MFB_DOWN_BLOCK_SIZE  (MFB_DOWN_BLOCK_SIZE) ,
        .MFB_DOWN_ITEM_WIDTH  (MFB_DOWN_ITEM_WIDTH) ,
        .DMA_MFB_DOWN_REGIONS (DMA_MFB_DOWN_REGIONS),
        .PCIE_UPHDR_WIDTH     (PCIE_UPHDR_WIDTH)    ,
        .PCIE_DOWNHDR_WIDTH   (PCIE_DOWNHDR_WIDTH)  ,
        .PCIE_PREFIX_WIDTH    (PCIE_PREFIX_WIDTH)   ,
        .DMA_TAG_WIDTH        ()                    ,
        .DMA_ID_WIDTH         ()                    ,
        .PCIE_TAG_WIDTH       (PCIE_TAG_WIDTH)      ,
        .MPS                  (MPS)                 ,
        .MRRS                 (MRRS)                ,
        .UP_ASFIFO_ITEMS      (UP_ASFIFO_ITEMS)     ,
        .DOWN_ASFIFO_ITEMS    (DOWN_ASFIFO_ITEMS)   ,
        .DOWN_FIFO_ITEMS      (DOWN_FIFO_ITEMS)     ,
        .RQ_TUSER_WIDTH       (RQ_TUSER_WIDTH)      ,
        .RC_TUSER_WIDTH       (RC_TUSER_WIDTH)      ,
        .AUTO_ASSIGN_TAGS     (AUTO_ASSIGN_TAGS)    ,
        .DEVICE               (DEVICE)              ,
        .ENDPOINT_TYPE        (ENDPOINT_TYPE)
    ) VHDL_DUT_U (
        //-------------------------------------------------------------------------
        // Common interface
        //-------------------------------------------------------------------------

        .CLK   (CLK)        ,
        .RESET (RST)  ,

        .CLK_DMA   (CLK_DMA),
        .RESET_DMA (RST_DMA),

        // ========================================================================
        // UPSTREAM interfaces
        // ========================================================================

        //-------------------------------------------------------------------------
        // Input from DMA Module (MVB+MFB bus) (runs on CLK_DMA)
        //-------------------------------------------------------------------------

        .UP_MVB_DATA    (up_mvb_data)   ,
        .UP_MVB_VLD     (up_mvb_vld)    ,
        .UP_MVB_SRC_RDY (up_mvb_src_rdy),
        .UP_MVB_DST_RDY (up_mvb_dst_rdy),

        .UP_MFB_DATA    (up_mfb_data)   ,
        .UP_MFB_SOF     (up_mfb_sof)    ,
        .UP_MFB_EOF     (up_mfb_eof)    ,
        .UP_MFB_SOF_POS (up_mfb_sof_pos),
        .UP_MFB_EOF_POS (up_mfb_eof_pos),
        .UP_MFB_SRC_RDY (up_mfb_src_rdy),
        .UP_MFB_DST_RDY (up_mfb_dst_rdy),

        //-------------------------------------------------------------------------
        // Output to PCIe Endpoint (Requester request interface (RQ))
        // Used in Xilinx DEVICEs
        //-------------------------------------------------------------------------

        // Data bus
        .RQ_TDATA  (AXI_RQ.TDATA) ,
        .RQ_TUSER  (AXI_RQ.TUSER) ,
        .RQ_TLAST  (AXI_RQ.TLAST) ,
        .RQ_TKEEP  (AXI_RQ.TKEEP) ,
        .RQ_TREADY (AXI_RQ.TREADY),
        .RQ_TVALID (AXI_RQ.TVALID),

        //-------------------------------------------------------------------------
        // Header output to PCIe Endpoint (Requester request interface (RQ))
        // Used in Intel DEVICEs with P_TILE Endpoint type
        //-------------------------------------------------------------------------

        .RQ_MVB_HDR_DATA    (RQ_MVB.DATA),
        .RQ_MVB_PREFIX_DATA ()           ,
        .RQ_MVB_VLD         (RQ_MVB.VLD) ,

        //-------------------------------------------------------------------------
        // Output to PCIe Endpoint (Requester request interface (RQ))
        // Used in Intel DEVICEs
        //-------------------------------------------------------------------------

        .RQ_MFB_DATA    (RQ_MFB.DATA)   ,
        .RQ_MFB_SOF     (RQ_MFB.SOF)    ,
        .RQ_MFB_EOF     (RQ_MFB.EOF)    ,
        .RQ_MFB_SOF_POS (rq_mfb_sof_pos),
        .RQ_MFB_EOF_POS (RQ_MFB.EOF_POS),
        .RQ_MFB_SRC_RDY (RQ_MFB.SRC_RDY),
        .RQ_MFB_DST_RDY (RQ_MFB.DST_RDY),

        // ========================================================================
        // DOWNSTREAM interfaces
        // ========================================================================

        //-------------------------------------------------------------------------
        // Header input from PCIe Endpoint (Requester Completion interface (RC))
        // Used in Intel DEVICEs with P_TILE Endpoint type
        //-------------------------------------------------------------------------

        .RC_MVB_HDR_DATA    (RC_MFB.META),
        .RC_MVB_PREFIX_DATA ()           ,
        .RC_MVB_VLD         (RC_MFB.SOF) ,

        //-------------------------------------------------------------------------
        // Input from PCIe Endpoint (Requester Completion Interface (RC))
        // Used in Intel DEVICEs
        //-------------------------------------------------------------------------

        .RC_MFB_DATA    (RC_MFB.DATA)   ,
        .RC_MFB_SOF     (RC_MFB.SOF)    ,
        .RC_MFB_EOF     (RC_MFB.EOF)    ,
        .RC_MFB_SOF_POS (rc_mfb_sof_pos),
        .RC_MFB_EOF_POS (RC_MFB.EOF_POS),
        .RC_MFB_SRC_RDY (RC_MFB.SRC_RDY),
        .RC_MFB_DST_RDY (RC_MFB.DST_RDY),

        //-------------------------------------------------------------------------
        // Input from PCIe Endpoint (Requester Completion Interface (RC))
        // Used in Xilinx DEVICEs
        //-------------------------------------------------------------------------

        .RC_TDATA  (AXI_RC.TDATA) ,
        .RC_TUSER  (AXI_RC.TUSER) ,
        .RC_TLAST  (AXI_RC.TLAST) ,
        .RC_TKEEP  (AXI_RC.TKEEP) ,
        .RC_TVALID (AXI_RC.TVALID),
        .RC_TREADY (AXI_RC.TREADY),

        //-------------------------------------------------------------------------
        // Output to DMA Module (MVB+MFB bus) (runs on CLK_DMA)
        //-------------------------------------------------------------------------

        .DOWN_MVB_DATA    (down_mvb_data)   ,
        .DOWN_MVB_VLD     (down_mvb_vld)    ,
        .DOWN_MVB_SRC_RDY (down_mvb_src_rdy),
        .DOWN_MVB_DST_RDY (down_mvb_dst_rdy),

        .DOWN_MFB_DATA    (down_mfb_data)   ,
        .DOWN_MFB_SOF     (down_mfb_sof)    ,
        .DOWN_MFB_EOF     (down_mfb_eof)    ,
        .DOWN_MFB_SOF_POS (down_mfb_sof_pos),
        .DOWN_MFB_EOF_POS (down_mfb_eof_pos),
        .DOWN_MFB_SRC_RDY (down_mfb_src_rdy),
        .DOWN_MFB_DST_RDY (down_mfb_dst_rdy),
        //-------------------------------------------------------------------------
        // Tag assigning interface to PCIe endpoint
        //-------------------------------------------------------------------------
        .RCB_SIZE         (RCB_SIZE),
        .TAG_ASSIGN       (),
        .TAG_ASSIGN_VLD   ()
    );


endmodule
