// dut.sv: Design under test
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Daniel Kriz <danielkriz@cesnet.cz>
//            Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

import test::*;

module DUT (
    input logic     CLK,
    input logic     RST,
    mfb_if.dut_rx   cq_mfb,
    mfb_if.dut_tx   usr_mfb,
    mi_if.dut_slave config_mi
);

    localparam USR_SOF_POS_WIDTH = (($clog2(USR_MFB_REGION_SIZE)*USR_MFB_REGIONS) == 0) ? (USR_MFB_REGIONS) : (USR_MFB_REGIONS*$clog2(USR_MFB_REGION_SIZE));
    localparam USR_EOF_POS_WIDTH = USR_MFB_REGIONS*$clog2(USR_MFB_REGION_SIZE*USR_MFB_BLOCK_SIZE);

    logic [$clog2(PKT_SIZE_MAX+1)-1:0] packet_size;
    logic [$clog2(CHANNELS)-1:0]       channel;
    logic [24-1:0]                     meta;
    logic [PCIE_CQ_MFB_REGIONS -1 : 0] cq_mfb_sof_int;

    generate
        //{packet_size, channel, meta} 24 + $clog2(PKT_SIZE_MAX+1) + $clog2(CHANNELS)[CHANNELS]
        assign usr_mfb.META[24 + $clog2(PKT_SIZE_MAX+1) + $clog2(CHANNELS)-1 -: $clog2(PKT_SIZE_MAX+1)] = packet_size[$clog2(PKT_SIZE_MAX+1)-1 -: $clog2(PKT_SIZE_MAX+1)];
        assign usr_mfb.META[24 + $clog2(CHANNELS)-1                          -: $clog2(CHANNELS)]       = channel[$clog2(CHANNELS)-1 -: $clog2(CHANNELS)]                ;
        assign usr_mfb.META[24 - 1                                           -: 24]                     = meta[24-1 -: 24]                                               ;
    endgenerate

    assign cq_mfb_sof_int = '0;

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

        .DMA_HDR_POINTER_WIDTH    (DMA_HDR_POINTER_WIDTH),
        .DATA_POINTER_WIDTH       (DATA_POINTER_WIDTH),
        .CHANNELS                 (CHANNELS),
        .CNTRS_WIDTH              (CNTRS_WIDTH),
        .HDR_META_WIDTH           (HDR_META_WIDTH),
        .PKT_SIZE_MAX             (PKT_SIZE_MAX)
    ) VHDL_DUT_U (
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

        .ST_SP_DBG_CHAN           (),
        .ST_SP_DBG_META           ()
    );
endmodule
