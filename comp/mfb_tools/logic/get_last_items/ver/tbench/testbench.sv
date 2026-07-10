/*!
 * \file testbench.sv
 * \brief Testbench
 * \author Jakub Cabal <cabal@cesnet.cz>
 * \date 2026
 */
 /*
 * Copyright (C) 2026 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

import test_pkg::*;

module testbench;

   logic CLK = 0;
   logic RESET;
   iMfbRx #(
      .REGIONS    (REGIONS),
      .REGION_SIZE(REGION_SIZE),
      .BLOCK_SIZE (BLOCK_SIZE),
      .ITEM_WIDTH (ITEM_WIDTH)
   ) RX (
      .CLK,
      .RESET
   );
   iMfbTx #(
      .REGIONS    (REGIONS),
      .REGION_SIZE(REGION_SIZE),
      .BLOCK_SIZE (BLOCK_SIZE),
      .ITEM_WIDTH (ITEM_WIDTH)
   ) TX (
      .CLK,
      .RESET
   );
   iMvbTx #(
      .ITEMS      (REGIONS),
      .ITEM_WIDTH (EXTRACTED_ITEMS*ITEM_WIDTH)
   ) EX (
      .CLK,
      .RESET
   );

   always begin
      #(CLK_PERIOD/2) CLK = ~CLK;
   end

   dut DUT_U (
      .CLK     (CLK),
      .RESET   (RESET),
      .RX      (RX),
      .TX      (TX),
      .EX      (EX)
   );

   TEST TEST_U (
      .CLK        (CLK),
      .RESET      (RESET),
      .RX         (RX),
      .TX         (TX),
      .TX_MONITOR (TX),
      .EX         (EX),
      .EX_MONITOR (EX)
   );

endmodule
