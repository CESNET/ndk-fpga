/*
 * discard_stat_ifc.sv: FrameLink Discard Stat Interface
 * Copyright (C) 2010 CESNET
 * Author(s): Marek Santa <santa@liberouter.org>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 * TODO:
 *
 */


// ----------------------------------------------------------------------------
//                         FrameLink Interface declaration
// ----------------------------------------------------------------------------
import math_pkg::*; //log2

// -- FrameLink Discard Stat Interface ----------------------------------------
interface iDiscardStat #(CHANNELS=2, STATUS_WIDTH=2) (input logic CLK, RESET);
  logic [log2(CHANNELS)-1:0] RX_CHAN        = 0;  // Input channel
  logic [CHANNELS-1:0]       DST_RDY_N         ;  // FL RX Destination Ready
  logic [log2(CHANNELS)-1:0] TX_CHAN           ;  // Output channel
  logic [CHANNELS*STATUS_WIDTH-1:0] STATUS     ;  // Status
  logic [CHANNELS*STATUS_WIDTH-1:0] BUF_STATUS ;  // Status

  clocking rx_cb @(posedge CLK);
    input  DST_RDY_N;
    output RX_CHAN;
  endclocking: rx_cb

  clocking tx_cb @(posedge CLK);
    input TX_CHAN;
  endclocking: tx_cb

  clocking stat_cb @(posedge CLK);
    output STATUS;
    input  BUF_STATUS;
  endclocking: stat_cb

  // DUT Modport
  modport dut (input  RX_CHAN,
               output DST_RDY_N,
               output TX_CHAN,
               input  STATUS,
               output BUF_STATUS);

  // Testbench Modports
  modport rx_tb   (clocking rx_cb);
  modport tx_tb   (clocking tx_cb);
  modport stat_tb (clocking stat_cb);

endinterface : iDiscardStat
