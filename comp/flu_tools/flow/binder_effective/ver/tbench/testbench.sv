/*
 * testbench.sv: Top Entity for automatic test
 * Copyright (C) 2012 CESNET
 * Author(s): Pavel Benacek <benacek@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 * TODO:
 *
 */


// ----------------------------------------------------------------------------
//                                 TESTBENCH
// ----------------------------------------------------------------------------
import test_pkg::*; // Test constants

module testbench;
   logic CLK = 0;
   logic RESET;
   iFrameLinkURx #(DATA_WIDTH,EOP_POS_WIDTH,SOP_POS_WIDTH)              RX[PORTS] (CLK, RESET);
   iFrameLinkURx #(HDR_WIDTH,HDR_EOP_POS_WIDTH, HDR_SOP_POS_WIDTH )     RXHDR[PORTS] (CLK,RESET);
   iFrameLinkUTx #(DATA_WIDTH,EOP_POS_WIDTH,SOP_POS_WIDTH)              TX (CLK, RESET);
   iFrameLinkUTx #(HDR_WIDTH,HDR_EOP_POS_WIDTH,HDR_SOP_POS_WIDTH)       TXHDR (CLK,RESET);

  //-- Clock generation -------------------------------------------------------
  always #(CLK_PERIOD/2) CLK = ~CLK;

  //-- Design Under Test ------------------------------------------------------
  DUT DUT_U   (.CLK     (CLK),
               .RESET   (RESET),
               .RX      (RX),
               .RXHDR   (RXHDR),
               .TX      (TX),
               .TXHDR   (TXHDR)
              );

  //-- Test -------------------------------------------------------------------
  TEST TEST_U (.CLK           (CLK),
               .RESET         (RESET),
               .RX            (RX),
               .RXHDR         (RXHDR),
               .TX            (TX),
               .MONITOR       (TX),
               .TXHDR         (TXHDR),
               .MONITORHDR    (TXHDR)
              );

endmodule : testbench
