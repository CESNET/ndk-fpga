// crossbarx_stream.vhd: Crossbarx stream
// Copyright (C) 2020 CESNET z. s. p. o.
// Author(s): Daniel Kriz <xkrizd01@vutbr.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

import test_pkg::*;

module DUT (
    input logic RX_CLK,
    input logic RX_CLK2,
    input logic RX_RESET,
    input logic TX_CLK,
    input logic TX_RESET,
    input logic CX_CLK_ARB,
    input logic CX_RESET_ARB,
    iMfbRx.dut RX,
    iMfbTx.dut TX
);

    DUT_WRAPPER #(
        .CX_USE_CLK2           (CX_USE_CLK2),
        .CX_USE_CLK_ARB        (CX_USE_CLK_ARB),
        .OBUF_META_EQ_OUTPUT   (OBUF_META_EQ_OUTPUT),
        .OBUF_INPUT_EQ_OUTPUT  (OBUF_INPUT_EQ_OUTPUT),

        .MFB_REGIONS           (MFB_REGIONS),
        .MFB_REGION_SIZE       (MFB_REGION_SIZE),
        .MFB_BLOCK_SIZE        (MFB_BLOCK_SIZE),
        .MFB_ITEM_WIDTH        (MFB_ITEM_WIDTH),
        .MFB_META_WIDTH        (MFB_META_WIDTH),

        .PKT_MTU               (PKT_MTU),
        .TRANS_FIFO_SIZE       (TRANS_FIFO_SIZE),
        .F_GAP_ADJUST_EN       (F_GAP_ADJUST_EN),
        .F_GAP_ADJUST_SIZE_AVG (F_GAP_ADJUST_SIZE_AVG),
        .F_GAP_ADJUST_SIZE_MIN (F_GAP_ADJUST_SIZE_MIN),

        .F_EXTEND_START_EN     (F_EXTEND_START_EN),
        .F_EXTEND_START_SIZE   (F_EXTEND_START_SIZE),
        .F_EXTEND_END_EN       (F_EXTEND_END_EN),
        .F_EXTEND_END_SIZE     (F_EXTEND_END_SIZE),

        .DEVICE                (DEVICE)
    ) VHDL_DUT_U (
        .RX_CLK                (RX_CLK),
        .RX_CLK2               (RX_CLK2),
        .RX_RESET              (RX_RESET),
        .TX_CLK                (TX_CLK),
        .TX_RESET              (TX_RESET),
        .CX_CLK_ARB            (CX_CLK_ARB),
        .CX_RESET_ARB          (CX_RESET_ARB),

        .RX_MFB_DATA           (RX.DATA),
        .RX_MFB_META           (RX.META),
        .RX_MFB_SOF_POS        (RX.SOF_POS),
        .RX_MFB_EOF_POS        (RX.EOF_POS),
        .RX_MFB_SOF            (RX.SOF),
        .RX_MFB_EOF            (RX.EOF),
        .RX_MFB_SRC_RDY        (RX.SRC_RDY),
        .RX_MFB_DST_RDY        (RX.DST_RDY),

        .TX_MFB_DATA           (TX.DATA),
        .TX_MFB_META           (TX.META),
        .TX_MFB_SOF_POS        (TX.SOF_POS),
        .TX_MFB_EOF_POS        (TX.EOF_POS),
        .TX_MFB_SOF            (TX.SOF),
        .TX_MFB_EOF            (TX.EOF),
        .TX_MFB_SRC_RDY        (TX.SRC_RDY),
        .TX_MFB_DST_RDY        (TX.DST_RDY)
    );

endmodule
