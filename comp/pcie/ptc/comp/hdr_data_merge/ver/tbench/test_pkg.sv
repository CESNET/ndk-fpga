/*!
 * \file test_pkg.sv
 * \brief Test Package
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

package test_pkg;

   import math_pkg::*;

   // Don't change MFB parameters!
   parameter MFB_REGIONS     = 2;
   parameter MFB_REGION_SIZE = 1;
   parameter MFB_BLOCK_SIZE  = 8;
   parameter MFB_ITEM_WIDTH  = 32;

   // Don't change MVB parameters!
   parameter MVB_ITEMS       = 2;
   parameter MVB_ITEM_WIDTH  = 129; // HDR width + 1

   // Generator parameters
   parameter PAYLOAD_RATE = 80; // payload rate in percent
   parameter PAYLOAD_SIZE_MAX = 64; // size is in dword (4bytes)
   parameter PAYLOAD_SIZE_MIN = 1; // size is in dword (4bytes)
   parameter TRANSACTION_COUNT = 10000;

   // Clock and reset parameters
   parameter DMA_CLK_PERIOD  = 5ns;
   parameter DMA_RESET_TIME  = 10*DMA_CLK_PERIOD;
   parameter PCIE_CLK_PERIOD = 4ns;
   parameter PCIE_RESET_TIME = 10*PCIE_CLK_PERIOD;

   // Helper parameters
   parameter HDR_WIDTH = MVB_ITEM_WIDTH-1;
   parameter HDR_SIZE  = HDR_WIDTH/MFB_ITEM_WIDTH;

   `include "custom_trans.sv"
   `include "scoreboard.sv"
   `include "custom_trans_gen.sv"

endpackage
