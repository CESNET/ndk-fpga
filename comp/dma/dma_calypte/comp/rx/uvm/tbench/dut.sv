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
        mfb_if.dut_tx   ptr_upd_mfb,
        mvb_if.dut_tx   ptr_upd_req_mvb,
        mi_if.dut_slave config_mi
    );

    // UVM_PROBE //
    bind RX_DMA_CALYPTE: VHDL_DUT_U probe_inf #(1) probe_discard((hdrm_dma_hdr_src_rdy & hdrm_dma_hdr_dst_rdy & (RESET === 1'b0)), hdrm_pkt_drop, CLK);

    logic [$clog2(CHANNELS)-1:0]       channel;
    logic [24-1:0]                     meta;
    logic [63:0]                       rx_stop_rq_buff_ba;
    logic                              rx_stop_rq_p2p_en;
    logic [POINTER_WIDTH-1:0]          rx_stop_rq_hdp;
    logic [POINTER_WIDTH-1:0]          rx_stop_rq_hhp;
    logic                              rx_stop_rq_en;
    logic                              rx_stop_rq_ack;

    assign channel[$clog2(CHANNELS)-1 -: $clog2(CHANNELS)]                 = usr_mfb.META[24 + $clog2(CHANNELS)-1                          -: $clog2(CHANNELS)];
    assign meta[24-1 -: 24]                                                = usr_mfb.META[24 -1                                            -: 24];

    logic [((PCIE_RQ_REGION_SIZE != 1) ? PCIE_RQ_REGIONS*$clog2(PCIE_RQ_REGION_SIZE) : PCIE_RQ_REGIONS*1)-1:0] pcie_rq_mfb_sof_pos;
    logic [((PCIE_RQ_REGION_SIZE != 1) ? PCIE_RQ_REGIONS*$clog2(PCIE_RQ_REGION_SIZE) : PCIE_RQ_REGIONS*1)-1:0] ptr_upd_mfb_sof_pos;
    generate
    if (PCIE_RQ_REGION_SIZE != 1) begin
        assign  pcie_rq_mfb.SOF_POS = pcie_rq_mfb_sof_pos;
        assign  ptr_upd_mfb.SOF_POS = ptr_upd_mfb_sof_pos;
    end else begin
        assign  pcie_rq_mfb.SOF_POS = '0;
        assign  ptr_upd_mfb.SOF_POS = '0;
    end
    endgenerate

    assign ptr_upd_req_mvb.DATA    = {rx_stop_rq_hhp, rx_stop_rq_hdp, rx_stop_rq_p2p_en, rx_stop_rq_buff_ba};
    assign ptr_upd_req_mvb.VLD     = 1'b1;
    assign ptr_upd_req_mvb.SRC_RDY = rx_stop_rq_en;
    assign ptr_upd_req_mvb.DST_RDY = rx_stop_rq_ack;

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

        .PTR_UPD_BUFF_BA  (rx_stop_rq_buff_ba),
        .PTR_UPD_P2P_EN   (rx_stop_rq_p2p_en),
        .PTR_UPD_HDP      (rx_stop_rq_hdp),
        .PTR_UPD_HHP      (rx_stop_rq_hhp),
        .PTR_UPD_DISP_EN  (rx_stop_rq_en),
        .PTR_UPD_DISP_ACK (rx_stop_rq_ack),

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

    // TODO: Radek does not like this and this should have its own verification
    DMA_PTR_UPDATER #(
        .DEVICE          (DEVICE),

        .MFB_REGIONS     (PCIE_RQ_REGIONS),
        .MFB_REGION_SIZE (PCIE_RQ_REGION_SIZE),
        .MFB_BLOCK_SIZE  (PCIE_RQ_BLOCK_SIZE),
        .MFB_ITEM_WIDTH  (PCIE_RQ_ITEM_WIDTH),

        .RX_CHANNELS  (CHANNELS),
        .RX_PTR_WIDTH (POINTER_WIDTH),

        .TX_CHANNELS       (CHANNELS),
        .TX_DATA_PTR_WIDTH (POINTER_WIDTH),
        .TX_HDR_PTR_WIDTH  (POINTER_WIDTH-3),
        .TX_UPD_THRESHOLD  (2**8)
    ) dma_ptr_updater_i (
        .CLK                (CLK),
        .RESET              (RST),

        .RX_STOP_REQ_BUFF_BA (rx_stop_rq_buff_ba),
        .RX_STOP_REQ_P2P_EN  (rx_stop_rq_p2p_en),
        .RX_STOP_REQ_HDP     (rx_stop_rq_hdp),
        .RX_STOP_REQ_HHP     (rx_stop_rq_hhp),
        .RX_STOP_REQ_EN      (rx_stop_rq_en),
        .RX_STOP_REQ_ACK     (rx_stop_rq_ack),

        .TX_RT_UPD_CH      (),
        .TX_RT_UPD_BUFF_BA (64'd0),
        .TX_RT_UPD_P2P_EN  (1'b0),

        .TX_PKT_DISP_CH ({$clog2(CHANNELS){1'b0}}),
        .TX_PKT_DISP_HDP({POINTER_WIDTH{1'b0}}),
        .TX_PKT_DISP_HHP({POINTER_WIDTH-3{1'b0}}),
        .TX_PKT_DISP_EN (1'b0),

        .TX_START_REQ_CH({$clog2(CHANNELS){1'b0}}),
        .TX_START_REQ_VLD(1'b0),
        .TX_START_REQ_ACK(),

        .TX_STOP_REQ_BUFF_BA (64'd0),
        .TX_STOP_REQ_P2P_EN  (1'b0),
        .TX_STOP_REQ_HDP     ({POINTER_WIDTH{1'b0}}),
        .TX_STOP_REQ_HHP     ({POINTER_WIDTH-3{1'b0}}),
        .TX_STOP_REQ_EN      (1'b0),
        .TX_STOP_REQ_ACK     (),

        .PCIE_RQ_MFB_DATA     (ptr_upd_mfb.DATA),
        .PCIE_RQ_MFB_META     (ptr_upd_mfb.META),
        .PCIE_RQ_MFB_SOF_POS  (ptr_upd_mfb_sof_pos),
        .PCIE_RQ_MFB_EOF_POS  (ptr_upd_mfb.EOF_POS),
        .PCIE_RQ_MFB_SOF      (ptr_upd_mfb.SOF),
        .PCIE_RQ_MFB_EOF      (ptr_upd_mfb.EOF),
        .PCIE_RQ_MFB_SRC_RDY  (ptr_upd_mfb.SRC_RDY),
        .PCIE_RQ_MFB_DST_RDY  (ptr_upd_mfb.DST_RDY)
    );
endmodule
