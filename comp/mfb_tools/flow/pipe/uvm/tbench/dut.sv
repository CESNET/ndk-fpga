//-- dut.sv: Design under test
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author:   David Beneš <xbenes52@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import test::*;

module DUT(
    input logic     CLK,
    input logic     RST,
    mfb_if.dut_rx   mfb_wr,
    mfb_if.dut_tx   mfb_rd
    );

    logic [((REGION_SIZE != 1) ? REGIONS*$clog2(REGION_SIZE) : REGIONS*1)-1:0] rx_sof_pos;
    logic [((REGION_SIZE != 1) ? REGIONS*$clog2(REGION_SIZE) : REGIONS*1)-1:0] tx_sof_pos;
    generate
        if (REGION_SIZE != 1) begin
            assign  mfb_rd.SOF_POS = tx_sof_pos;
            assign  rx_sof_pos = mfb_wr.SOF_POS;
        end
    endgenerate


    MFB_PIPE#(
        .REGIONS        (REGIONS),
        .REGION_SIZE    (REGION_SIZE),
        .BLOCK_SIZE     (BLOCK_SIZE),
        .ITEM_WIDTH     (ITEM_WIDTH),
        .META_WIDTH     (META_WIDTH),
        .FAKE_PIPE      (FAKE_PIPE),
        .USE_DST_RDY    (USE_DST_RDY),
        .PIPE_TYPE      (PIPE_TYPE),
        .DEVICE         (DEVICE)
    ) VHDL_DUT_U(
        .CLK            (CLK),
        .RESET          (RST),

        .RX_DATA        (mfb_wr.DATA),
        .RX_META        (mfb_wr.META),
        .RX_SOF_POS     (rx_sof_pos),
        .RX_EOF_POS     (mfb_wr.EOF_POS),
        .RX_SOF         (mfb_wr.SOF),
        .RX_EOF         (mfb_wr.EOF),
        .RX_SRC_RDY     (mfb_wr.SRC_RDY),
        .RX_DST_RDY     (mfb_wr.DST_RDY),

        .TX_DATA        (mfb_rd.DATA),
        .TX_META        (mfb_rd.META),
        .TX_SOF_POS     (tx_sof_pos),
        .TX_EOF_POS     (mfb_rd.EOF_POS),
        .TX_SOF         (mfb_rd.SOF),
        .TX_EOF         (mfb_rd.EOF),
        .TX_SRC_RDY     (mfb_rd.SRC_RDY),
        .TX_DST_RDY     (mfb_rd.DST_RDY)
    );

endmodule
