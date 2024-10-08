/*!
 * \file testbench.sv
 * \brief Testbench
 * \author Jakub Cabal <cabal@cesnet.cz>
 * \date 2018
 */
 /*
 * Copyright (C) 2018 CESNET z. s. p. o.
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

   iMvbRx #(REGIONS,LEN_WIDTH) RX_MVB(CLK, RESET);
   iMfbTx #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) TX_MFB(CLK, RESET);

   always #(CLK_PERIOD/2) CLK = ~CLK;

   DUT DUT_U (
      .CLK    (CLK),
      .RESET  (RESET),
      .RX_MVB (RX_MVB),
      .TX_MFB (TX_MFB)
   );

   TEST TEST_U (
      .CLK     (CLK),
      .RESET   (RESET),
      .RX_MVB  (RX_MVB),
      .TX_MFB  (TX_MFB),
      .MONITOR (TX_MFB)
   );

endmodule
