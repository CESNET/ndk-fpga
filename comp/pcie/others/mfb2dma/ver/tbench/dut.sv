/*!
 * \file dut.sv
 * \brief Design Under Test
 * \author Jakub Cabal <cabal@cesnet.cz>
 * \date 2018
 */
 /*
 * Copyright (C) 2018 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

import test_pkg::*;

module DUT (
    input logic CLK,
    input logic RESET,
    iMvbRx.dut RX_MVB,
    iMfbRx.dut RX_MFB,
    iDMABusTx.dut TX_DMA
);

    MFB2DMA #(
        .MVB_ITEMS       (MVB_ITEMS),
        .MFB_REGIONS     (MFB_REGIONS),
        .MFB_REG_WIDTH   (MFB_REG_WIDTH),
        .INPUT_FIFO_SIZE (INPUT_FIFO_SIZE)
    ) VHDL_DUT_U (
        .CLK                 (CLK),
        .RESET               (RESET),

        .RX_MVB_DOWN_HDR     (RX_MVB.DATA),
        .RX_MVB_DOWN_VLD     (RX_MVB.VLD),
        .RX_MVB_DOWN_SRC_RDY (RX_MVB.SRC_RDY),
        .RX_MVB_DOWN_DST_RDY (RX_MVB.DST_RDY),

        .RX_MFB_DOWN_DATA    (RX_MFB.DATA),
        .RX_MFB_DOWN_SOF     (RX_MFB.SOF),
        .RX_MFB_DOWN_EOF     (RX_MFB.EOF),
        .RX_MFB_DOWN_SRC_RDY (RX_MFB.SRC_RDY),
        .RX_MFB_DOWN_DST_RDY (RX_MFB.DST_RDY),

        .TX_DMA_DOWN_HDR     (TX_DMA.HDR),
        .TX_DMA_DOWN_DATA    (TX_DMA.DATA),
        .TX_DMA_DOWN_SOP     (TX_DMA.SOP),
        .TX_DMA_DOWN_EOP     (TX_DMA.EOP),
        .TX_DMA_DOWN_SRC_RDY (TX_DMA.SRC_RDY),
        .TX_DMA_DOWN_DST_RDY (TX_DMA.DST_RDY)
    );

endmodule
