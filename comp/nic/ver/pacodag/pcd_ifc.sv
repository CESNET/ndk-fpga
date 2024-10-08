/*
 * pcd_ifc.sv: PACODAG Interface
 * Copyright (C) 2009 CESNET
 * Author(s): Marek Santa <xsanta06@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 * TODO:
 *
 */


// ----------------------------------------------------------------------------
//                       PACODAG Interface declaration
// ----------------------------------------------------------------------------
import math_pkg::*;

// -- PACODAG Interface -----------------------------------------------------
interface iPacodag #(DATA_WIDTH = 64) (input logic CLK, RESET);
  logic [DATA_WIDTH-1:0]         DATA       = 0; // Control data
  logic [log2(DATA_WIDTH/8)-1:0] REM        = 0; // Data reminder
  logic                          SRC_RDY_N  = 1; // Source ready
  logic                          DST_RDY_N    ;  // Destination ready
  logic                          SOP_N      = 1; // Start of part
  logic                          EOP_N      = 1; // End of part
  logic                          SOP          ;  // Request control data
  logic                          RDY        = 1; // Control data generator is ready to receive new request
  logic                          STAT_FRAME_ERR; // Incoming protocol error
  logic                          STAT_MAC_ERR  ; // MAC address not accepted
  logic                          STAT_MINTU_ERR; // Frame doesn't have minimal length
  logic                          STAT_MTU_ERR  ; // Frame exceeds maximal length
  logic                          STAT_CRC_ERR  ; // Frame has bad CRC
  logic [15:0]                   STAT_FRAME_LEN; // Frame length
  logic                          STAT_DV       ; // Statistics are valid


  clocking cb @(posedge CLK);
    output DATA, REM, SRC_RDY_N, SOP_N, EOP_N, RDY;
    input  DST_RDY_N, SOP, STAT_FRAME_ERR, STAT_MAC_ERR, STAT_MINTU_ERR,
           STAT_MTU_ERR, STAT_CRC_ERR, STAT_FRAME_LEN, STAT_DV;
  endclocking: cb;

  clocking monitor_cb @(posedge CLK);
    input  DATA, REM, SRC_RDY_N, SOP_N, EOP_N, RDY,
           DST_RDY_N, SOP, STAT_FRAME_ERR, STAT_MAC_ERR, STAT_MINTU_ERR,
           STAT_MTU_ERR, STAT_CRC_ERR, STAT_FRAME_LEN, STAT_DV;
  endclocking: monitor_cb;

  // Receive Modport
  modport dut ( input  DATA,
                input  REM,
                input  SRC_RDY_N,
                input  SOP_N,
                input  EOP_N,
                input  RDY,
                output DST_RDY_N,
                output SOP,
                output STAT_FRAME_ERR,
                output STAT_MAC_ERR,
                output STAT_MINTU_ERR,
                output STAT_MTU_ERR,
                output STAT_CRC_ERR,
                output STAT_FRAME_LEN,
                output STAT_DV);

  // Transitive Modport
  modport tb (clocking cb);

  // Monitor Modport
  modport monitor (clocking monitor_cb);


  // --------------------------------------------------------------------------
  // -- Interface properties/assertions
  // --------------------------------------------------------------------------

  // -- No data after EOP_N ---------------------------------------------------
  // After EOP_N, data cannot be sent, until SOP_N is sent. EOP_N marks end of
  // transaction. First, we define a sequence of waiting for the first active
  // SOP_N. Then we declare, that after active cycle of EOP_N, there may be no
  // transfer during that sequence ( = until active SOP_N).

  sequence sop_seq;
     ##[0:$] (!SOP_N) && !(SRC_RDY_N || DST_RDY_N);
  endsequence

  property NoDataAfterEOP;
     @(posedge CLK) disable iff (RESET)
        (!EOP_N) && !(SRC_RDY_N || DST_RDY_N) |=>
	   !(SOP_N && !(SRC_RDY_N || DST_RDY_N)) throughout sop_seq;
  endproperty

  assert property (NoDataAfterEOP)
     else $error("Pacodag transaction continued after PCD_EOP_N.");


  // -- Matching EOP_N after SOP_N --------------------------------------------
  // Each SOP_N must be, after some time, followed by EOP_N. Each transaction
  // must have its end. First, we define a sequence of waiting for the first
  // active EOP_N. Then we declare, that after active cycle of SOP_N, there
  // may be no another active SOP_N during that sequence ( = until active
  // EOP_N).
  sequence eop_seq;
     ##[0:$] (!EOP_N) && !(SRC_RDY_N || DST_RDY_N);
  endsequence

  property EOPMatchSOP;
     @(posedge CLK) disable iff (RESET)
        (!SOP_N) && EOP_N && !(SRC_RDY_N || DST_RDY_N) |=>
           (!((!SOP_N) && !(SRC_RDY_N || DST_RDY_N))) throughout eop_seq;
  endproperty

  assert property (EOPMatchSOP)
     else $error("PCD_SOP_N was not followed by matching PCD_EOP_N.");


  // -- Matching STAT_DV after SOP --------------------------------------------
  // Valid SOP must go before STAT_DV. First, we define a sequence of waiting
  // for the first valid SOP. Then we declare, that after invalid cycle of
  // SOP ( = without active RDY), there may be no active STAT_DV during that
  // sequence ( = until valid SOP).
  sequence valid_sop_seq;
     ##[0:$] (SOP) && (RDY);
  endsequence

  property SOPGoBeforeSTATDV;
     @(posedge CLK) disable iff (RESET)
        (SOP) && !(RDY) |=>
           (!STAT_DV) throughout valid_sop_seq;
  endproperty

  assert property (SOPGoBeforeSTATDV)
     else $error("PCD_STAT_DV was active without PCD_SOP.");


endinterface : iPacodag
