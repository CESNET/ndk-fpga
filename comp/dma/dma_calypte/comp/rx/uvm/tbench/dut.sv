//-- dut.sv: Design under test
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


module DMA_LL_DUT #(DEVICE, USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE, USR_MFB_ITEM_WIDTH, PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE, PCIE_RQ_BLOCK_SIZE, PCIE_RQ_ITEM_WIDTH, CHANNELS, PKT_SIZE_MAX, SW_ADDR_WIDTH, POINTER_WIDTH, CNTRS_WIDTH, TRBUF_REG_EN, PERF_CNTR_EN)
    (
        input logic     CLK,
        input logic     RST,
        mfb_if.dut_rx   usr_mfb,
        mfb_if.dut_tx   pcie_rq_mfb,
        mi_if.dut_slave config_mi
    );

    // UVM_PROBE //
    bind RX_DMA_CALYPTE: VHDL_DUT_U probe_inf #(1) probe_discard((hdrm_dma_hdr_src_rdy & hdrm_dma_hdr_dst_rdy & (RESET === 1'b0)), hdrm_pkt_drop, CLK);

    logic [$clog2(CHANNELS)-1:0]       channel;
    logic [24-1:0]                     meta;

    assign channel[$clog2(CHANNELS)-1 -: $clog2(CHANNELS)]                 = usr_mfb.META[24 + $clog2(CHANNELS)-1                          -: $clog2(CHANNELS)];
    assign meta[24-1 -: 24]                                                = usr_mfb.META[24 -1                                            -: 24];

    logic [((PCIE_RQ_REGION_SIZE != 1) ? PCIE_RQ_REGIONS*$clog2(PCIE_RQ_REGION_SIZE) : PCIE_RQ_REGIONS*1)-1:0] pcie_rq_mfb_sof_pos;
    generate
    if (PCIE_RQ_REGION_SIZE != 1) begin
        assign  pcie_rq_mfb.SOF_POS = pcie_rq_mfb_sof_pos;
    end
    endgenerate

    RX_DMA_CALYPTE #(
        .DEVICE           (DEVICE),
        .USER_RX_MFB_REGIONS     (USR_MFB_REGIONS),
        .USER_RX_MFB_REGION_SIZE (USR_MFB_REGION_SIZE),
        .USER_RX_MFB_BLOCK_SIZE  (USR_MFB_BLOCK_SIZE),
        .USER_RX_MFB_ITEM_WIDTH  (USR_MFB_ITEM_WIDTH),

        .PCIE_UP_MFB_REGIONS     (PCIE_RQ_REGIONS),
        .PCIE_UP_MFB_REGION_SIZE (PCIE_RQ_REGION_SIZE),
        .PCIE_UP_MFB_BLOCK_SIZE  (PCIE_RQ_BLOCK_SIZE),
        .PCIE_UP_MFB_ITEM_WIDTH  (PCIE_RQ_ITEM_WIDTH),

        .CHANNELS      (CHANNELS),
        .POINTER_WIDTH (POINTER_WIDTH),
        .SW_ADDR_WIDTH (SW_ADDR_WIDTH),
        .CNTRS_WIDTH   (CNTRS_WIDTH),
        .PKT_SIZE_MAX  (PKT_SIZE_MAX),
        .TRBUF_REG_EN  (TRBUF_REG_EN),
        .PERF_CNTR_EN  (PERF_CNTR_EN)
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

        .USER_RX_MFB_DATA        (usr_mfb.DATA),
        .USER_RX_MFB_SOF_POS     (usr_mfb.SOF_POS),
        .USER_RX_MFB_EOF_POS     (usr_mfb.EOF_POS),
        .USER_RX_MFB_SOF         (usr_mfb.SOF),
        .USER_RX_MFB_EOF         (usr_mfb.EOF),
        .USER_RX_MFB_SRC_RDY     (usr_mfb.SRC_RDY),
        .USER_RX_MFB_DST_RDY     (usr_mfb.DST_RDY),

        .PCIE_UP_MFB_DATA     (pcie_rq_mfb.DATA),
        .PCIE_UP_MFB_META     (pcie_rq_mfb.META),
        .PCIE_UP_MFB_SOF_POS  (pcie_rq_mfb_sof_pos),
        .PCIE_UP_MFB_EOF_POS  (pcie_rq_mfb.EOF_POS),
        .PCIE_UP_MFB_SOF      (pcie_rq_mfb.SOF),
        .PCIE_UP_MFB_EOF      (pcie_rq_mfb.EOF),
        .PCIE_UP_MFB_SRC_RDY  (pcie_rq_mfb.SRC_RDY),
        .PCIE_UP_MFB_DST_RDY  (pcie_rq_mfb.DST_RDY)
    );
endmodule
