//-- dut.sv: Design under test
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


module DMA_LL_DUT #(DEVICE, USER_REGIONS, USER_REGION_SIZE, USER_BLOCK_SIZE, USER_ITEM_WIDTH, PCIE_UP_REGIONS, PCIE_UP_REGION_SIZE, PCIE_UP_BLOCK_SIZE, PCIE_UP_ITEM_WIDTH, CHANNELS, PKT_SIZE_MAX, SW_ADDR_WIDTH, POINTER_WIDTH, CNTRS_WIDTH, OPT_BUFF, TRBUF_REG_EN)
    (
        input logic     CLK,
        input logic     RST,
        mfb_if.dut_rx   mfb_rx,
        mfb_if.dut_tx   mfb_tx,
        mi_if.dut_slave config_mi
    );

    // UVM_PROBE //
    bind RX_DMA_CALYPTE: VHDL_DUT_U probe_inf #(1) probe_discard((hdrm_dma_hdr_src_rdy & hdrm_dma_hdr_dst_rdy & (RESET === 1'b0)), hdrm_pkt_drop, CLK);

    logic [$clog2(CHANNELS)-1:0]       channel;
    logic [24-1:0]                     meta;

    assign channel[$clog2(CHANNELS)-1 -: $clog2(CHANNELS)]                 = mfb_rx.META[24 + $clog2(CHANNELS)-1                          -: $clog2(CHANNELS)];
    assign meta[24-1 -: 24]                                                = mfb_rx.META[24 -1                                            -: 24];

    logic [((PCIE_UP_REGION_SIZE != 1) ? PCIE_UP_REGIONS*$clog2(PCIE_UP_REGION_SIZE) : PCIE_UP_REGIONS*1)-1:0] sof_pos;
    generate
    if (PCIE_UP_REGION_SIZE != 1) begin
        assign  mfb_tx.SOF_POS = sof_pos;
    end
    endgenerate

    RX_DMA_CALYPTE #(
        .DEVICE           (DEVICE),
        .USER_RX_MFB_REGIONS     (USER_REGIONS),
        .USER_RX_MFB_REGION_SIZE (USER_REGION_SIZE),
        .USER_RX_MFB_BLOCK_SIZE  (USER_BLOCK_SIZE),
        .USER_RX_MFB_ITEM_WIDTH  (USER_ITEM_WIDTH),

        .PCIE_UP_MFB_REGIONS     (PCIE_UP_REGIONS),
        .PCIE_UP_MFB_REGION_SIZE (PCIE_UP_REGION_SIZE),
        .PCIE_UP_MFB_BLOCK_SIZE  (PCIE_UP_BLOCK_SIZE),
        .PCIE_UP_MFB_ITEM_WIDTH  (PCIE_UP_ITEM_WIDTH),

        .CHANNELS      (CHANNELS),
        .POINTER_WIDTH (POINTER_WIDTH),
        .SW_ADDR_WIDTH (SW_ADDR_WIDTH),
        .CNTRS_WIDTH   (CNTRS_WIDTH),
        .PKT_SIZE_MAX  (PKT_SIZE_MAX),
        .TRBUF_FIFO_EN (OPT_BUFF),
        .TRBUF_REG_EN  (TRBUF_REG_EN)
    ) VHDL_DUT_U (
        .CLK                (CLK),
        .RESET              (RST),

        .MI_ADDR            (config_mi.ADDR),
        .MI_DWR             (config_mi.DWR),
        .MI_BE              (config_mi.BE),
        .MI_RD              (config_mi.RD),
        .MI_WR              (config_mi.WR),
        .MI_DRD             (config_mi.DRD),
        .MI_ARDY            (config_mi.ARDY),
        .MI_DRDY            (config_mi.DRDY),

        .USER_RX_MFB_META_HDR_META    (meta),
        .USER_RX_MFB_META_CHAN        (channel),

        .USER_RX_MFB_DATA        (mfb_rx.DATA),
        .USER_RX_MFB_SOF_POS     (mfb_rx.SOF_POS),
        .USER_RX_MFB_EOF_POS     (mfb_rx.EOF_POS),
        .USER_RX_MFB_SOF         (mfb_rx.SOF),
        .USER_RX_MFB_EOF         (mfb_rx.EOF),
        .USER_RX_MFB_SRC_RDY     (mfb_rx.SRC_RDY),
        .USER_RX_MFB_DST_RDY     (mfb_rx.DST_RDY),

        .PCIE_UP_MFB_DATA     (mfb_tx.DATA),
        .PCIE_UP_MFB_META     (mfb_tx.META),
        .PCIE_UP_MFB_SOF_POS  (sof_pos),
        .PCIE_UP_MFB_EOF_POS  (mfb_tx.EOF_POS),
        .PCIE_UP_MFB_SOF      (mfb_tx.SOF),
        .PCIE_UP_MFB_EOF      (mfb_tx.EOF),
        .PCIE_UP_MFB_SRC_RDY  (mfb_tx.SRC_RDY),
        .PCIE_UP_MFB_DST_RDY  (mfb_tx.DST_RDY)
    );
endmodule
