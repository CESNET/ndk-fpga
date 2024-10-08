/*
 * testbench.sv: Top-level verification testbench
 * Copyright (C) 2018 CESNET
 * Author(s): Lukas Kekely <kekely@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

import test_pkg::*; // Test constants



module testbench;
  logic CLK = 0;
  logic RESET;
  iFrameLinkUTx #(DATA_WIDTH, EOP_POS_WIDTH, SOP_POS_WIDTH) TX (CLK, RESET);
  iMi32 MI (CLK, RESET);

  // Clock generation
  always #(CLK_PERIOD/2) CLK = ~CLK;

  DUT DUT_U (
    .CLK     (CLK),
    .RESET   (RESET),
    .TX      (TX),
    .MI      (MI)
  );

  TEST TEST_U (
    .CLK          (CLK),
    .RESET        (RESET),
    .TX           (TX),
    .MONITOR      (TX),
    .MI           (MI)
  );

endmodule
