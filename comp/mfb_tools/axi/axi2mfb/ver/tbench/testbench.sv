/* testbench.sv: testbench
 * Copyright (C) 2024 DynaNIC Semiconductors, Ltd.
 * Author(s): Radek Hajek <hajek@dyna-nic.com>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

import test_pkg::*;

module testbench;

    logic CLK = 0;
    logic RESET;
    iMfbTx #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH,META_WIDTH) TX (CLK, RESET);
    iAxi4SRx #(AXI_DATA_WIDTH, AXI_USER_WIDTH, ITEM_WIDTH) RX (CLK, RESET);

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
