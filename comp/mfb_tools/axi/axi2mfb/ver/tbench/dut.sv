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
    iAxi4SRx.dut RX,
    iMfbTx.dut TX
);

    AXI2MFB #(
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

        .RX_AXI_TDATA   (RX.TDATA),
        .RX_AXI_TKEEP   (RX.TKEEP),
        .RX_AXI_TLAST   (RX.TLAST),
        .RX_AXI_TVALID  (RX.TVALID),
        .RX_AXI_TREADY  (RX.TREADY),

        .TX_MFB_DATA    (TX.DATA),
        .TX_MFB_SOF_POS (TX.SOF_POS),
        .TX_MFB_EOF_POS (TX.EOF_POS),
        .TX_MFB_SOF     (TX.SOF),
        .TX_MFB_EOF     (TX.EOF),
        .TX_MFB_SRC_RDY (TX.SRC_RDY),
        .TX_MFB_DST_RDY (TX.DST_RDY)
    );

endmodule
