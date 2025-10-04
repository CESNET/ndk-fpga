// dut.sv: Design under test
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Daniel Kriz <danielkriz@cesnet.cz>
//            Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

import test::*;

module dut (
    input logic     CLK,
    input logic     RST,
    mfb_if.dut_rx   cq_mfb,
    mfb_if.dut_tx   usr_mfb,
    mfb_if.dut_tx   ptr_upd_mfb,
    mvb_if.dut_tx   upd_stop_req_mvb,
    mvb_if.dut_tx   chan_start_req_mvb,
    mvb_if.dut_tx   rt_upd_mvb,
    mi_if.dut_slave config_mi
);

    localparam USR_SOF_POS_WIDTH = (($clog2(USR_MFB_REGION_SIZE)*USR_MFB_REGIONS) == 0) ? (USR_MFB_REGIONS)
               : (USR_MFB_REGIONS*$clog2(USR_MFB_REGION_SIZE));
    localparam USR_EOF_POS_WIDTH = USR_MFB_REGIONS*$clog2(USR_MFB_REGION_SIZE*USR_MFB_BLOCK_SIZE);

    logic [$clog2(PKT_SIZE_MAX+1)-1:0] packet_size;
    logic [$clog2(CHANNELS)-1:0]       channel;
    logic [24-1:0]                     meta;
    logic [PCIE_CQ_MFB_REGIONS -1 : 0] cq_mfb_sof_int;

    logic [$clog2(CHANNELS)-1 : 0]     tx_rt_upd_ch;
    logic [63 : 0]                     tx_rt_upd_buff_ba;
    logic                              tx_rt_udp_p2p_en;

    logic [$clog2(CHANNELS)-1 : 0]     tx_pkt_disp_ch;
    logic [DATA_POINTER_WIDTH-1 : 0]   tx_pkt_disp_hdp;
    logic [DATA_POINTER_WIDTH-3-1 : 0] tx_pkt_disp_hhp;
    logic                              tx_pkt_disp_en;

    logic [$clog2(CHANNELS)-1 : 0]     tx_start_req_ch;
    logic                              tx_start_req_vld;
    logic                              tx_start_req_ack;

    logic [63:0]                       tx_stop_rq_buff_ba;
    logic                              tx_stop_rq_p2p_en;
    logic [DATA_POINTER_WIDTH-1:0]     tx_stop_rq_hdp;
    logic [DATA_POINTER_WIDTH-3-1:0]   tx_stop_rq_hhp;
    logic                              tx_stop_rq_en;
    logic                              tx_stop_rq_ack;

    logic [((PCIE_CQ_MFB_REGION_SIZE != 1) ? PCIE_CQ_MFB_REGIONS*$clog2(PCIE_CQ_MFB_REGION_SIZE) :
            PCIE_CQ_MFB_REGIONS*1)-1:0] ptr_upd_mfb_sof_pos;

    generate
    if (PCIE_CQ_MFB_REGION_SIZE != 1) begin
        assign  ptr_upd_mfb.SOF_POS = ptr_upd_mfb_sof_pos;
    end else begin
        assign  ptr_upd_mfb.SOF_POS = '0;
    end
    endgenerate

    generate
        //{packet_size, channel, meta} 24 + $clog2(PKT_SIZE_MAX+1) + $clog2(CHANNELS)[CHANNELS]
        assign usr_mfb.META[24 + $clog2(PKT_SIZE_MAX+1) + $clog2(CHANNELS)-1 -: $clog2(PKT_SIZE_MAX+1)]
            = packet_size[$clog2(PKT_SIZE_MAX+1)-1 -: $clog2(PKT_SIZE_MAX+1)];
        assign usr_mfb.META[24 + $clog2(CHANNELS)-1 -: $clog2(CHANNELS)]
            = channel[$clog2(CHANNELS)-1 -: $clog2(CHANNELS)];
        assign usr_mfb.META[24-1 -: 24]
            = meta[24-1 -: 24];
    endgenerate

    assign cq_mfb_sof_int       = '0;
    assign upd_stop_req_mvb.DATA    = {tx_stop_rq_hhp, tx_stop_rq_hdp, tx_stop_rq_p2p_en, tx_stop_rq_buff_ba};
    assign upd_stop_req_mvb.VLD     = 1'b1;
    assign upd_stop_req_mvb.SRC_RDY = tx_stop_rq_en;
    assign upd_stop_req_mvb.DST_RDY = tx_stop_rq_ack;

    assign chan_start_req_mvb.DATA    = tx_start_req_ch;
    assign chan_start_req_mvb.VLD     = 1'b1;
    assign chan_start_req_mvb.SRC_RDY = tx_start_req_vld;
    assign chan_start_req_mvb.DST_RDY = tx_start_req_ack;

    assign rt_upd_mvb.DATA    = {tx_pkt_disp_hhp, tx_pkt_disp_hdp, tx_pkt_disp_ch};
    assign rt_upd_mvb.VLD     = 1'b1;
    assign rt_upd_mvb.SRC_RDY = tx_pkt_disp_en;
    assign rt_upd_mvb.DST_RDY = 1'b1;

    TX_DMA_CALYPTE #(
        .DEVICE                   (DEVICE),

        .MI_WIDTH                 (MI_WIDTH),

        .USR_TX_MFB_REGIONS       (USR_MFB_REGIONS),
        .USR_TX_MFB_REGION_SIZE   (USR_MFB_REGION_SIZE),
        .USR_TX_MFB_BLOCK_SIZE    (USR_MFB_BLOCK_SIZE),
        .USR_TX_MFB_ITEM_WIDTH    (USR_MFB_ITEM_WIDTH),

        .PCIE_CQ_MFB_REGIONS      (PCIE_CQ_MFB_REGIONS),
        .PCIE_CQ_MFB_REGION_SIZE  (PCIE_CQ_MFB_REGION_SIZE),
        .PCIE_CQ_MFB_BLOCK_SIZE   (PCIE_CQ_MFB_BLOCK_SIZE),
        .PCIE_CQ_MFB_ITEM_WIDTH   (PCIE_CQ_MFB_ITEM_WIDTH),

        .CHANNELS                 (CHANNELS),
        .POINTER_WIDTH            (DATA_POINTER_WIDTH),
        .CNTRS_WIDTH              (CNTRS_WIDTH),
        .HDR_META_WIDTH           (HDR_META_WIDTH),
        .PKT_SIZE_MAX             (PKT_SIZE_MAX)
    ) vhdl_dut_i (
        .CLK                      (CLK),
        .RESET                    (RST),

        .MI_ADDR                  (config_mi.ADDR),
        .MI_DWR                   (config_mi.DWR),
        .MI_BE                    (config_mi.BE),
        .MI_RD                    (config_mi.RD),
        .MI_WR                    (config_mi.WR),
        .MI_DRD                   (config_mi.DRD),
        .MI_ARDY                  (config_mi.ARDY),
        .MI_DRDY                  (config_mi.DRDY),

        .USR_TX_MFB_META_PKT_SIZE (packet_size),
        .USR_TX_MFB_META_CHAN     (channel),
        .USR_TX_MFB_META_HDR_META (meta),

        .USR_TX_MFB_DATA          (usr_mfb.DATA),
        .USR_TX_MFB_SOF           (usr_mfb.SOF),
        .USR_TX_MFB_EOF           (usr_mfb.EOF),
        .USR_TX_MFB_SOF_POS       (usr_mfb.SOF_POS),
        .USR_TX_MFB_EOF_POS       (usr_mfb.EOF_POS),
        .USR_TX_MFB_SRC_RDY       (usr_mfb.SRC_RDY),
        .USR_TX_MFB_DST_RDY       (usr_mfb.DST_RDY),

        .PCIE_CQ_MFB_DATA         (cq_mfb.DATA),
        .PCIE_CQ_MFB_META         (cq_mfb.META),
        .PCIE_CQ_MFB_SOF_POS      (cq_mfb_sof_int),
        .PCIE_CQ_MFB_EOF_POS      (cq_mfb.EOF_POS),
        .PCIE_CQ_MFB_SOF          (cq_mfb.SOF),
        .PCIE_CQ_MFB_EOF          (cq_mfb.EOF),
        .PCIE_CQ_MFB_SRC_RDY      (cq_mfb.SRC_RDY),
        .PCIE_CQ_MFB_DST_RDY      (cq_mfb.DST_RDY),

        .RT_UPD_CH               (tx_rt_upd_ch),
        .RT_UPD_BUFF_BA          (tx_rt_upd_buff_ba),
        .RT_UPD_P2P_EN           (tx_rt_udp_p2p_en),

        .PKT_DISP_UPD_CH          (tx_pkt_disp_ch),
        .PKT_DISP_UPD_HDP         (tx_pkt_disp_hdp),
        .PKT_DISP_UPD_HHP         (tx_pkt_disp_hhp),
        .PKT_DISP_UPD_EN          (tx_pkt_disp_en),

        .PTR_UPD_START_REQ_CH     (tx_start_req_ch),
        .PTR_UPD_START_REQ_VLD    (tx_start_req_vld),
        .PTR_UPD_START_REQ_ACK    (tx_start_req_ack),

        .PTR_UPD_STOP_REQ_BUFF_BA (tx_stop_rq_buff_ba),
        .PTR_UPD_STOP_REQ_P2P_EN  (tx_stop_rq_p2p_en),
        .PTR_UPD_STOP_REQ_HDP     (tx_stop_rq_hdp),
        .PTR_UPD_STOP_REQ_HHP     (tx_stop_rq_hhp),
        .PTR_UPD_STOP_REQ_EN      (tx_stop_rq_en),
        .PTR_UPD_STOP_REQ_ACK     (tx_stop_rq_ack),

        .ST_SP_DBG_CHAN           (),
        .ST_SP_DBG_META           ()
    );

    DMA_PTR_UPDATER #(
        .DEVICE          (DEVICE),

        .MFB_REGIONS     (PCIE_CQ_MFB_REGIONS),
        .MFB_REGION_SIZE (PCIE_CQ_MFB_REGION_SIZE),
        .MFB_BLOCK_SIZE  (PCIE_CQ_MFB_BLOCK_SIZE),
        .MFB_ITEM_WIDTH  (PCIE_CQ_MFB_ITEM_WIDTH),

        .RX_CHANNELS  (CHANNELS),
        .RX_PTR_WIDTH (16),

        .TX_CHANNELS       (CHANNELS),
        .TX_DATA_PTR_WIDTH (DATA_POINTER_WIDTH),
        .TX_HDR_PTR_WIDTH  (DATA_POINTER_WIDTH-3),
        .TX_UPD_THRESHOLD  (UPD_THRESHOLD)
    ) dma_ptr_updater_i (
        .CLK                (CLK),
        .RESET              (RST),

        .RX_STOP_REQ_BUFF_BA (64'd0),
        .RX_STOP_REQ_P2P_EN  (1'b0),
        .RX_STOP_REQ_HDP     ({16{1'b0}}),
        .RX_STOP_REQ_HHP     ({16{1'b0}}),
        .RX_STOP_REQ_EN      (1'b0),
        .RX_STOP_REQ_ACK     (),

        .TX_RT_UPD_CH        (tx_rt_upd_ch),
        .TX_RT_UPD_BUFF_BA   (tx_rt_upd_buff_ba),
        .TX_RT_UPD_P2P_EN    (tx_rt_udp_p2p_en),

        .TX_PKT_DISP_CH      (tx_pkt_disp_ch),
        .TX_PKT_DISP_HDP     (tx_pkt_disp_hdp),
        .TX_PKT_DISP_HHP     (tx_pkt_disp_hhp),
        .TX_PKT_DISP_EN      (tx_pkt_disp_en),

        .TX_START_REQ_CH     (tx_start_req_ch),
        .TX_START_REQ_VLD    (tx_start_req_vld),
        .TX_START_REQ_ACK    (tx_start_req_ack),

        .TX_STOP_REQ_BUFF_BA (tx_stop_rq_buff_ba),
        .TX_STOP_REQ_P2P_EN  (tx_stop_rq_p2p_en),
        .TX_STOP_REQ_HDP     (tx_stop_rq_hdp),
        .TX_STOP_REQ_HHP     (tx_stop_rq_hhp),
        .TX_STOP_REQ_EN      (tx_stop_rq_en),
        .TX_STOP_REQ_ACK     (tx_stop_rq_ack),

        .PCIE_RQ_MFB_DATA    (ptr_upd_mfb.DATA),
        .PCIE_RQ_MFB_META    (ptr_upd_mfb.META),
        .PCIE_RQ_MFB_SOF_POS (ptr_upd_mfb_sof_pos),
        .PCIE_RQ_MFB_EOF_POS (ptr_upd_mfb.EOF_POS),
        .PCIE_RQ_MFB_SOF     (ptr_upd_mfb.SOF),
        .PCIE_RQ_MFB_EOF     (ptr_upd_mfb.EOF),
        .PCIE_RQ_MFB_SRC_RDY (ptr_upd_mfb.SRC_RDY),
        .PCIE_RQ_MFB_DST_RDY (ptr_upd_mfb.DST_RDY)
    );
endmodule
