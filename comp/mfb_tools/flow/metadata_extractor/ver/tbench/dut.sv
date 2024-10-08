/*!
 * \file dut.sv
 * \brief Design Under Test
 * \author Daniel Kriz <xkrizd01@vutbr.cz>
 * \date 2020
 */
 /*
 * Copyright (C) 2020 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */


module DUT (
    input logic CLK,
    input logic RESET,
    iMfbRx.dut RX,
    iMfbTx.dut TX_MFB,
    iMvbTx.dut TX_MVB
);

    METADATA_EXTRACTOR #(
        // MVB characteristics
        .MVB_ITEMS       (test_pkg::MVB_ITEMS),
        // MFB characteristics
        .MFB_REGIONS     (test_pkg::MFB_REGIONS),
        .MFB_REGION_SIZE (test_pkg::MFB_REGION_SIZE),
        .MFB_BLOCK_SIZE  (test_pkg::MFB_BLOCK_SIZE),
        .MFB_ITEM_WIDTH  (test_pkg::MFB_ITEM_WIDTH),
        .MFB_META_WIDTH  (test_pkg::MFB_META_WIDTH),
        // Others
        .EXTRACT_MODE    (test_pkg::EXTRACT_MODE),
        .OUT_MVB_PIPE_EN (test_pkg::OUT_MVB_PIPE_EN),
        .OUT_MFB_PIPE_EN (test_pkg::OUT_MFB_PIPE_EN)
    ) VHDL_DUT_U (
        .CLK             (CLK),
        .RESET           (RESET),
        // RX MFB INTERFACE
        .RX_MFB_DATA     (RX.DATA),
        .RX_MFB_META     (RX.META),
        .RX_MFB_SOF_POS  (RX.SOF_POS),
        .RX_MFB_EOF_POS  (RX.EOF_POS),
        .RX_MFB_SOF      (RX.SOF),
        .RX_MFB_EOF      (RX.EOF),
        .RX_MFB_SRC_RDY  (RX.SRC_RDY),
        .RX_MFB_DST_RDY  (RX.DST_RDY),
        // TX MFB INTERFACE
        .TX_MFB_DATA     (TX_MFB.DATA),
        .TX_MFB_META     (TX_MFB.META),
        .TX_MFB_SOF_POS  (TX_MFB.SOF_POS),
        .TX_MFB_EOF_POS  (TX_MFB.EOF_POS),
        .TX_MFB_SOF      (TX_MFB.SOF),
        .TX_MFB_EOF      (TX_MFB.EOF),
        .TX_MFB_SRC_RDY  (TX_MFB.SRC_RDY),
        .TX_MFB_DST_RDY  (TX_MFB.DST_RDY),
        // TX MVB INTERFACE
        .TX_MVB_DATA     (TX_MVB.DATA),
        .TX_MVB_VLD      (TX_MVB.VLD),
        .TX_MVB_SRC_RDY  (TX_MVB.SRC_RDY),
        .TX_MVB_DST_RDY  (TX_MVB.DST_RDY)
    );

endmodule
