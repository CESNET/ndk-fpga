// dut.sv: Design under test
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s):  Mikuláš Brázda <xbrazd21@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


import test::*;

module DUT (
    input logic     CLK,
    input logic     RESET,
    mfb_if.dut_rx   mfb_rx,
    mfb_if.dut_tx   mfb_tx
    );

    logic [REGIONS*(REGION_SIZE <= 1 ? 1 : $clog2(REGION_SIZE))-1:0] rx_sof_pos;


    logic [REGIONS*(REGION_SIZE <= 1 ? 1 : $clog2(REGION_SIZE))-1:0] tx_sof_pos;

    generate
        if (REGION_SIZE > 1) begin
            assign rx_sof_pos = mfb_rx.SOF_POS;
            assign mfb_tx.SOF_POS = tx_sof_pos;
        end else begin
            assign rx_sof_pos = 'x;
        end
    endgenerate


    MFB_FIFOX #(
        .REGIONS         (REGIONS),
        .REGION_SIZE     (REGION_SIZE),
        .BLOCK_SIZE      (BLOCK_SIZE),
        .ITEM_WIDTH      (ITEM_WIDTH),
        .META_WIDTH      (META_WIDTH),
        .FIFO_DEPTH      (FIFO_DEPTH),
        .RAM_TYPE        (RAM_TYPE),
        .DEVICE          (DEVICE)
    ) VHDL_DUT_U (
        .CLK                (CLK),
        .RST              (RESET),
        .RX_DATA        (mfb_rx.DATA),
        .RX_META        (mfb_rx.META),
        .RX_SOF_POS     (rx_sof_pos),
        .RX_EOF_POS     (mfb_rx.EOF_POS),
        .RX_SOF         (mfb_rx.SOF),
        .RX_EOF         (mfb_rx.EOF),
        .RX_SRC_RDY     (mfb_rx.SRC_RDY),
        .RX_DST_RDY     (mfb_rx.DST_RDY),

        .TX_DATA        (mfb_tx.DATA),
        .TX_META        (mfb_tx.META),
        .TX_SOF_POS     (tx_sof_pos),
        .TX_EOF_POS     (mfb_tx.EOF_POS),
        .TX_SOF         (mfb_tx.SOF),
        .TX_EOF         (mfb_tx.EOF),
        .TX_SRC_RDY     (mfb_tx.SRC_RDY),
        .TX_DST_RDY     (mfb_tx.DST_RDY)

    );


endmodule

