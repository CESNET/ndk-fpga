//-- dut.sv: Design under test
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import test::*;

module dut (
    input logic     CLK    ,
    input logic     CLK_DMA,
    input logic     RST    ,
    input logic     RST_DMA,
    // UPSTREAM
    mfb_if.dut_rx   DMA_RX_MFB[DMA_PORTS]  ,
    mvb_if.dut_rx   DMA_RX_MVB[DMA_PORTS]  ,
    mfb_if.dut_tx   RQ_MFB             ,
    mvb_if.dut_tx   RQ_MVB             ,
    //reset_if.dut    RST             //,
    // DOWNSTREAM
    mfb_if.dut_rx   RC_MFB             ,
    mfb_if.dut_tx   DMA_TX_MFB[DMA_PORTS],
    mvb_if.dut_tx   DMA_TX_MVB[DMA_PORTS],
    // AXI
    axi_if.dut_tx   AXI_RQ,
    axi_if.dut_rx   AXI_RC
    );

    localparam IS_INTEL = (DEVICE == "STRATIX10" ||  DEVICE == "AGILEX") ? 1'b1 : 1'b0;
    localparam RQ_AXI_ITEMS = (IS_INTEL == 0) ? MFB_UP_REGIONS*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE       : 16;
    localparam RC_AXI_ITEMS = (IS_INTEL == 0) ? MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE : 16;
    localparam ITEM_WIDTH = 32;
    localparam DOWN_SOF_POS_WIDTH = (($clog2(
        MFB_DOWN_REG_SIZE
    ) * DMA_MFB_DOWN_REGIONS) == 0) ? (DMA_MFB_DOWN_REGIONS) : (DMA_MFB_DOWN_REGIONS * $clog2(
        MFB_DOWN_REG_SIZE
    ));
    localparam DOWN_EOF_POS_WIDTH = DMA_MFB_DOWN_REGIONS*$clog2(MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE);
    localparam UP_SOF_POS_WIDTH = (($clog2(
        MFB_UP_REG_SIZE
    ) * DMA_MFB_UP_REGIONS) == 0) ? (DMA_MFB_UP_REGIONS) : (DMA_MFB_UP_REGIONS * $clog2(
        MFB_UP_REG_SIZE
    ));
    localparam UP_EOF_POS_WIDTH   = DMA_MFB_UP_REGIONS*$clog2(MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE);
    localparam RQ_SOF_POS_WIDTH = (($clog2(
        MFB_UP_REG_SIZE
    ) * MFB_UP_REGIONS) == 0) ? (MFB_UP_REGIONS) : (MFB_UP_REGIONS * $clog2(
        MFB_UP_REG_SIZE
    ));
    localparam RC_SOF_POS_WIDTH = (($clog2(
        MFB_DOWN_REG_SIZE
    ) * MFB_DOWN_REGIONS) == 0) ? (MFB_DOWN_REGIONS) : (MFB_DOWN_REGIONS * $clog2(
        MFB_DOWN_REG_SIZE
    ));

    // verilog_lint: waive line-length
    logic [DMA_MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE*ITEM_WIDTH -1:0]           down_mfb_data     [DMA_PORTS-1:0];
    // verilog_lint: waive line-length
    logic [DMA_MFB_DOWN_REGIONS -1:0]                                                            down_mfb_sof      [DMA_PORTS-1:0];
    // verilog_lint: waive line-length
    logic [DMA_MFB_DOWN_REGIONS -1:0]                                                            down_mfb_eof      [DMA_PORTS-1:0];
    // verilog_lint: waive line-length
    logic [DOWN_SOF_POS_WIDTH -1:0]                                                              down_mfb_sof_pos  [DMA_PORTS-1:0];
    // verilog_lint: waive line-length
    logic [DOWN_EOF_POS_WIDTH -1:0]                                                              down_mfb_eof_pos  [DMA_PORTS-1:0];
    logic [DMA_PORTS-1:0]                                                                        down_mfb_src_rdy;
    logic [DMA_PORTS-1:0]                                                                        down_mfb_dst_rdy;

    // verilog_lint: waive line-length
    logic [DMA_MFB_UP_REGIONS*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE*ITEM_WIDTH -1:0]                 up_mfb_data     [DMA_PORTS-1:0];
    // verilog_lint: waive line-length
    logic [DMA_MFB_UP_REGIONS -1:0]                                                              up_mfb_sof      [DMA_PORTS-1:0];
    // verilog_lint: waive line-length
    logic [DMA_MFB_UP_REGIONS -1:0]                                                              up_mfb_eof      [DMA_PORTS-1:0];
    // verilog_lint: waive line-length
    logic [UP_SOF_POS_WIDTH -1:0]                                                                up_mfb_sof_pos  [DMA_PORTS-1:0];
    // verilog_lint: waive line-length
    logic [UP_EOF_POS_WIDTH -1:0]                                                                up_mfb_eof_pos  [DMA_PORTS-1:0];
    logic [DMA_PORTS-1:0]                                                                        up_mfb_src_rdy;
    logic [DMA_PORTS-1:0]                                                                        up_mfb_dst_rdy;

    logic [DMA_PORTS-1:0]                                                                        up_mvb_src_rdy;
    logic [DMA_PORTS-1:0]                                                                        up_mvb_dst_rdy;
    // verilog_lint: waive line-length
    logic [DMA_MVB_UP_ITEMS*sv_dma_bus_pack::DMA_UPHDR_WIDTH-1 : 0]                              up_mvb_data     [DMA_PORTS-1:0];
    // verilog_lint: waive line-length
    logic [DMA_MVB_UP_ITEMS-1 : 0]                                                               up_mvb_vld      [DMA_PORTS-1:0];

    logic [DMA_PORTS-1:0]                                                                        down_mvb_src_rdy;
    logic [DMA_PORTS-1:0]                                                                        down_mvb_dst_rdy;
    // verilog_lint: waive line-length
    logic [DMA_MVB_DOWN_ITEMS*sv_dma_bus_pack::DMA_DOWNHDR_WIDTH-1 : 0]                          down_mvb_data     [DMA_PORTS-1:0];
    // verilog_lint: waive line-length
    logic [DMA_MVB_DOWN_ITEMS-1 : 0]                                                             down_mvb_vld      [DMA_PORTS-1:0];

    logic [RQ_SOF_POS_WIDTH -1:0]                                                                rq_mfb_sof_pos;
    logic [RC_SOF_POS_WIDTH -1:0]                                                                rc_mfb_sof_pos;


    logic [MFB_UP_REGIONS*sv_pcie_meta_pack::PCIE_META_REQ_HDR_W-1 : 0] pcie_rq_hdr;
    logic [MFB_UP_REGIONS*32-1 : 0]               pcie_rq_prefix;

    logic [MFB_DOWN_REGIONS*sv_pcie_meta_pack::PCIE_META_CPL_HDR_W-1 : 0] pcie_rc_hdr;
    logic [MFB_DOWN_REGIONS*32-1 : 0]              pcie_rc_prefix;


    logic [MFB_UP_REGIONS*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE*ITEM_WIDTH-1:0]       axi_rq_data;
    logic [MFB_UP_REGIONS*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE-1:0]                  axi_rq_keep;
    logic [MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE*ITEM_WIDTH-1:0] axi_rc_data;
    logic [MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE-1:0]            axi_rc_keep;
    // PCIE_AXI doesnt support more that 32 DWORDS.
    generate
        if (IS_INTEL == 0) begin : gen_IS_INTEL_0
            assign AXI_RQ.TDATA = axi_rq_data;
            assign AXI_RQ.TKEEP = axi_rq_keep;
            assign axi_rc_data = AXI_RC.TDATA;
            assign axi_rc_keep = AXI_RC.TKEEP;
        end
    endgenerate

    generate
        for (genvar it = 0; it < MFB_UP_REGIONS; it++) begin : gen_rq_it
            assign
                RQ_MVB.DATA[(it+1)*(sv_pcie_meta_pack::PCIE_RQ_META_WIDTH)-1-:sv_pcie_meta_pack::PCIE_RQ_META_WIDTH] =
                // LBE, FBE, PREFIX, HDR
                {4'b1111, 4'b1111,
                    pcie_rq_prefix[(it+1)*32-1 -: 32],
                    pcie_rq_hdr[(it+1)*sv_pcie_meta_pack::PCIE_META_REQ_HDR_W-1-:sv_pcie_meta_pack::PCIE_META_REQ_HDR_W]
                };
        end

        for (genvar it = 0; it < MFB_UP_REGIONS; it++) begin : gen_rc_it
            assign {
                        pcie_rc_prefix[(it+1)*32-1 -: 32],
                pcie_rc_hdr[(it+1)*sv_pcie_meta_pack::PCIE_META_CPL_HDR_W-1-:sv_pcie_meta_pack::PCIE_META_CPL_HDR_W]
                } =
                RC_MFB.META[(it+1)*(sv_pcie_meta_pack::PCIE_RC_META_WIDTH)-1-:sv_pcie_meta_pack::PCIE_RC_META_WIDTH];
        end
    endgenerate


    generate
        for (genvar i = 0; i < DMA_PORTS; i++) begin : gen_i
            assign DMA_TX_MFB[i].DATA    = down_mfb_data[i];
            assign DMA_TX_MFB[i].SOF     = down_mfb_sof[i];
            assign DMA_TX_MFB[i].EOF     = down_mfb_eof[i];
            assign DMA_TX_MFB[i].SOF_POS = down_mfb_sof_pos[i];
            assign DMA_TX_MFB[i].EOF_POS = down_mfb_eof_pos[i];
            assign DMA_TX_MFB[i].SRC_RDY = down_mfb_src_rdy[i];
            assign down_mfb_dst_rdy[i] = DMA_TX_MFB[i].DST_RDY;

            assign up_mfb_data[i]      = DMA_RX_MFB[i].DATA;
            assign up_mfb_sof[i]       = DMA_RX_MFB[i].SOF;
            assign up_mfb_eof[i]       = DMA_RX_MFB[i].EOF;

            if ((DMA_MFB_UP_REGIONS*$clog2(MFB_UP_REG_SIZE)) == 0) begin : gen_DMA_MFB_UP_REGIONS_clog2_MFB_UP_REG_SIZE
                assign up_mfb_sof_pos[i] = '0;
            end else begin : gen_DMA_MFB_UP_REGIONS_clog2_MFB_UP_REG_SIZE_nonzero
                assign up_mfb_sof_pos[i]   = DMA_RX_MFB[i].SOF_POS;
            end
            assign up_mfb_eof_pos[i]   = DMA_RX_MFB[i].EOF_POS;
            assign up_mfb_src_rdy[i]   = DMA_RX_MFB[i].SRC_RDY;
            assign DMA_RX_MFB[i].DST_RDY   = up_mfb_dst_rdy[i];

            assign up_mvb_data   [i]   = DMA_RX_MVB[i].DATA;
            assign up_mvb_vld    [i]   = DMA_RX_MVB[i].VLD;
            assign up_mvb_src_rdy[i]   = DMA_RX_MVB[i].SRC_RDY;
            assign DMA_RX_MVB[i].DST_RDY   = up_mvb_dst_rdy[i];

            assign DMA_TX_MVB[i].DATA    = down_mvb_data[i];
            assign DMA_TX_MVB[i].VLD     = down_mvb_vld[i];
            assign DMA_TX_MVB[i].SRC_RDY = down_mvb_src_rdy[i];
            assign down_mvb_dst_rdy[i] = DMA_TX_MVB[i].DST_RDY;

        end
    endgenerate

    if (DEVICE == "STRATIX10" || DEVICE == "AGILEX") begin : gen_DEVICE_STRATIX10_DEVICE_AGILEX
        assign RQ_MVB.SRC_RDY      = RQ_MFB.SRC_RDY;
        assign RQ_MVB.DST_RDY      = RQ_MFB.DST_RDY;
    end
    assign RQ_MFB.SOF_POS      = rq_mfb_sof_pos;

    if ((DMA_MFB_DOWN_REGIONS*$clog2(MFB_DOWN_REG_SIZE)) == 0) begin : gen_DMA_MFB_DOWN_REGIONS_clog2_MFB_DOWN_REG_
        assign rc_mfb_sof_pos = '0;
    end else begin : gen_DMA_MFB_DOWN_REGIONS_clog2_MFB_DOWN_REG_SIZE_nonzero
        assign rc_mfb_sof_pos = RC_MFB.SOF_POS;
    end
    PCIE_TRANSACTION_CTRL_WRAPPER #(
        .DMA_PORTS            (DMA_PORTS)           ,
        .MVB_UP_ITEMS         (MVB_UP_ITEMS)        ,
        .DMA_MVB_UP_ITEMS     (DMA_MVB_UP_ITEMS)    ,
        .MFB_UP_REGIONS       (MFB_UP_REGIONS)      ,
        .MFB_UP_REG_SIZE      (MFB_UP_REG_SIZE)     ,
        .MFB_UP_BLOCK_SIZE    (MFB_UP_BLOCK_SIZE)   ,
        .MFB_UP_ITEM_WIDTH    (ITEM_WIDTH)   ,
        .DMA_MFB_UP_REGIONS   (DMA_MFB_UP_REGIONS)  ,
        .MVB_DOWN_ITEMS       (MVB_DOWN_ITEMS)      ,
        .DMA_MVB_DOWN_ITEMS   (DMA_MVB_DOWN_ITEMS)  ,
        .MFB_DOWN_REGIONS     (MFB_DOWN_REGIONS)    ,
        .MFB_DOWN_REG_SIZE    (MFB_DOWN_REG_SIZE)   ,
        .MFB_DOWN_BLOCK_SIZE  (MFB_DOWN_BLOCK_SIZE) ,
        .MFB_DOWN_ITEM_WIDTH  (ITEM_WIDTH) ,
        .DMA_MFB_DOWN_REGIONS (DMA_MFB_DOWN_REGIONS),
        .PCIE_UPHDR_WIDTH     (sv_pcie_meta_pack::PCIE_META_REQ_HDR_W),
        .PCIE_DOWNHDR_WIDTH   (sv_pcie_meta_pack::PCIE_META_CPL_HDR_W),
        .PCIE_PREFIX_WIDTH    (PCIE_PREFIX_WIDTH)   ,
        .DMA_TAG_WIDTH        ()                    ,
        .DMA_ID_WIDTH         ()                    ,
        .PCIE_TAG_WIDTH       (PCIE_TAG_WIDTH)      ,
        .MPS                  (MPS)                 ,
        .MRRS                 (MRRS)                ,
        .UP_ASFIFO_ITEMS      (UP_ASFIFO_ITEMS)     ,
        .DOWN_ASFIFO_ITEMS    (DOWN_ASFIFO_ITEMS)   ,
        .DOWN_FIFO_ITEMS      (DOWN_FIFO_ITEMS)     ,
        .RQ_TUSER_WIDTH       (uvm_pcie_axi::tuser_width_get(RQ_AXI_ITEMS, uvm_pcie_axi::AXI_RQ)),
        .RC_TUSER_WIDTH       (uvm_pcie_axi::tuser_width_get(RC_AXI_ITEMS, uvm_pcie_axi::AXI_RC)),
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
        .RQ_TDATA  (axi_rq_data) ,
        .RQ_TUSER  (AXI_RQ.TUSER) ,
        .RQ_TLAST  (AXI_RQ.TLAST) ,
        .RQ_TKEEP  (axi_rq_keep) ,
        .RQ_TREADY (AXI_RQ.TREADY),
        .RQ_TVALID (AXI_RQ.TVALID),

        //-------------------------------------------------------------------------
        // Header output to PCIe Endpoint (Requester request interface (RQ))
        // Used in Intel DEVICEs with P_TILE Endpoint type
        //-------------------------------------------------------------------------

        .RQ_MVB_HDR_DATA    (pcie_rq_hdr),
        .RQ_MVB_PREFIX_DATA (pcie_rq_prefix),
        .RQ_MVB_VLD         (RQ_MVB.VLD),

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

        .RC_MVB_HDR_DATA    (pcie_rc_hdr),
        .RC_MVB_PREFIX_DATA (pcie_rc_prefix),
        .RC_MVB_VLD         (RC_MFB.SOF),

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

        .RC_TDATA  (axi_rc_data) ,
        .RC_TUSER  (AXI_RC.TUSER) ,
        .RC_TLAST  (AXI_RC.TLAST) ,
        .RC_TKEEP  (axi_rc_keep) ,
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
