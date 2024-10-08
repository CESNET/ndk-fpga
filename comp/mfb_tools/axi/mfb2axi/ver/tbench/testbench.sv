/* testbench.sv: testbench
 * Copyright (C) 2024 BrnoLogic, Ltd.
 * Author(s): Radek Hajek <hajek@brnologic.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

import test_pkg::*;

module testbench;

    logic CLK = 0;
    logic RESET;
    iMfbRx #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) RX (CLK, RESET);
    iAxi4STx #(AXI_DATA_WIDTH, META_WIDTH, 8) TX (CLK, RESET); // AXI is always byte oriented

    always #(CLK_PERIOD/2) CLK = ~CLK;

    DUT DUT_U (
        .CLK     (CLK),
        .RESET   (RESET),
        .RX      (RX),
        .TX      (TX)
    );

    TEST TEST_U (
        .CLK     (CLK),
        .RESET   (RESET),
        .RX      (RX),
        .TX      (TX),
        .MONITOR (TX)
    );

endmodule
