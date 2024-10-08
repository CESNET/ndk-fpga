/* dut.sv: DUT module
 * Copyright (C) 2024 BrnoLogic, Ltd.
 * Author(s): Radek Hajek <hajek@brnologic.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

import test_pkg::*;

module DUT (
    input logic CLK,
    input logic RESET,
    iMfbRx.dut RX,
    iAxi4STx.dut TX
);

    MFB2AXI #(
        .USE_IN_PIPE     (USE_IN_PIPE),
        .USE_OUT_PIPE    (USE_OUT_PIPE),
        .REGIONS         (REGIONS),
        .REGION_SIZE     (REGION_SIZE),
        .BLOCK_SIZE      (BLOCK_SIZE),
        .ITEM_WIDTH      (ITEM_WIDTH),
        .AXI_DATA_WIDTH  (AXI_DATA_WIDTH),
        .PIPE_TYPE       (PIPE_TYPE),
        .DEVICE          (DEVICE)
    ) VHDL_DUT_U (
        .CLK            (CLK),
        .RST            (RESET),

        .TX_AXI_TDATA   (TX.TDATA),
        .TX_AXI_TKEEP   (TX.TKEEP),
        .TX_AXI_TLAST   (TX.TLAST),
        .TX_AXI_TVALID  (TX.TVALID),
        .TX_AXI_TREADY  (TX.TREADY),

        .RX_MFB_DATA    (RX.DATA),
        .RX_MFB_SOF_POS (RX.SOF_POS),
        .RX_MFB_EOF_POS (RX.EOF_POS),
        .RX_MFB_SOF     (RX.SOF),
        .RX_MFB_EOF     (RX.EOF),
        .RX_MFB_SRC_RDY (RX.SRC_RDY),
        .RX_MFB_DST_RDY (RX.DST_RDY)

    );

endmodule
