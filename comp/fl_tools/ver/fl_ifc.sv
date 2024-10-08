/*
 * fl_ifc.pkg: FrameLink Interface
 * Copyright (C) 2008 CESNET
 * Author(s): Marcela Simkova <xsimko03@stud.fit.vutbr.cz>
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

// -- FrameLink Interface -----------------------------------------------------
interface iFrameLinkRx #(DWIDTH=32, DREMWIDTH=2) (input logic CLK, RESET);
  logic [DWIDTH-1:0] DATA    = 0;  // Data
  logic [DREMWIDTH-1:0] DREM = 0;  // Data Reminder
  logic SOF_N                = 1;  // Start of Frame active in low
  logic EOF_N                = 1;  // End of Frame active in low
  logic SOP_N                = 1;  // Start of Packet active in low
  logic EOP_N                = 1;  // End of Packet active in low
  logic SRC_RDY_N            = 1;  // Source data ready active in low
  logic DST_RDY_N;                 // Destination data ready active in low


  clocking cb @(posedge CLK);
    input  DST_RDY_N;
    output DATA, DREM, SOF_N, EOF_N, SOP_N, EOP_N, SRC_RDY_N;
  endclocking: cb;

  // Receive Modport
  modport dut (input  DATA,
               input  DREM,
               input  SOF_N,
               input  EOF_N,
               input  SOP_N,
               input  EOP_N,
               input  SRC_RDY_N,
               output DST_RDY_N);

  // Transitive Modport
  modport tb (clocking cb);


  // --------------------------------------------------------------------------
  // -- Interface properties/assertions
  // --------------------------------------------------------------------------

  // -- While RESET SRC_RDY_N inactive ----------------------------------------
  // SRC_RDY_N may be active only if RESET is inactive.

  property RESETSRC;
     @(posedge CLK) (RESET)|->(SRC_RDY_N);
  endproperty

  assert property (RESETSRC)
     else $error("RX_SRC_RDY_N is active during reset.");

  // -- SOF together with SOP -------------------------------------------------
  // SOF may be active only if SOP is active.

  property SOFSOP;
     @(posedge CLK) !(SOF_N) && !(SRC_RDY_N)|->!(SOP_N);
  endproperty

  assert property (SOFSOP)
     else $error("RX_SOF_N is not active the same time as RX_SOP_N.");


  // -- EOF together with EOP -------------------------------------------------
  // EOF may be active only if EOP is active.

  property EOFEOP;
     @(posedge CLK) !(EOF_N) && !(SRC_RDY_N)|->!(EOP_N);
  endproperty

  assert property (EOFEOP)
     else $error("RX_EOF_N is not active the same time as RX_EOP_N.");


  // -- No data after EOP ----------------------------------------------------
  // After EOP, data cannot be sent, until SOP is sent. EOP marks end of
  // transaction. First, we define a sequence of waiting for the first active
  // SOP. Then we declare, that after active cycle of EOP, there may be no
  // transfer during that sequence ( = until active SOP).

  sequence sop_seq;
     ##[0:$] (!SOP_N) && !(SRC_RDY_N || DST_RDY_N);
  endsequence

  property NoDataAfterEOP;
     @(posedge CLK) disable iff (RESET)
        (!EOP_N) && !(SRC_RDY_N || DST_RDY_N) |=>
	   !(SOP_N && !(SRC_RDY_N || DST_RDY_N)) throughout sop_seq;
  endproperty

  assert property (NoDataAfterEOP)
     else $error("FrameLink transaction continued after RX_EOP_N.");


  // -- Matching EOP after SOP ------------------------------------------------
  // Each SOP must be, after some time, followed by EOP. Each transaction must
  // have its end. First, we define a sequence of waiting for the first active
  // EOP. Then we declare, that after active cycle of SOP, there may be no
  // another active SOP during that sequence ( = until active EOP).
  sequence eop_seq;
     ##[0:$] (!EOP_N) && !(SRC_RDY_N || DST_RDY_N);
  endsequence

  property EOPMatchSOP;
     @(posedge CLK) disable iff (RESET)
        (!SOP_N) && EOP_N && !(SRC_RDY_N || DST_RDY_N) |=>
           (!((!SOP_N) && !(SRC_RDY_N || DST_RDY_N))) throughout eop_seq;
  endproperty

  assert property (EOPMatchSOP)
     else $error("RX_SOP_N was not followed by matching RX_EOP_N.");


  // -- Matching EOF after SOF ------------------------------------------------
  // Each SOF must be, after some time, followed by EOF. Each transaction must
  // have its end. First, we define a sequence of waiting for the first active
  // EOF. Then we declare, that after active cycle of SOF, there may be no
  // another active SOF during that sequence ( = until active EOF).
  sequence eof_seq;
     ##[0:$] (!EOF_N) && !(SRC_RDY_N || DST_RDY_N);
  endsequence

  property EOFMatchSOF;
     @(posedge CLK) disable iff (RESET)
        (!SOF_N) && (EOF_N) && !(SRC_RDY_N || DST_RDY_N) |=>
           (!((!SOF_N) && !(SRC_RDY_N || DST_RDY_N))) throughout eof_seq;
  endproperty

  assert property (EOFMatchSOF)
     else $error("RX_SOF_N was not followed by matching RX_EOF_N.");

endinterface : iFrameLinkRx



// -- FrameLink Interface -----------------------------------------------------
interface iFrameLinkTx #(DWIDTH=32, DREMWIDTH=2) (input logic CLK, RESET);
  logic [DWIDTH-1:0] DATA;     // Data
  logic [DREMWIDTH-1:0] DREM;  // Data Reminder
  logic SOF_N;                 // Start of Frame active in low
  logic EOF_N;                 // End of Frame active in low
  logic SOP_N;                 // Start of Packet active in low
  logic EOP_N;                 // End of Packet active in low
  logic SRC_RDY_N;             // Source data ready active in low
  logic DST_RDY_N = 1;         // Destination data ready active in low


  clocking cb @(posedge CLK);
    output  DST_RDY_N;
    input DATA, DREM, SOF_N, EOF_N, SOP_N, EOP_N, SRC_RDY_N;
  endclocking: cb;

  clocking monitor_cb @(posedge CLK);
    input DATA, DREM, SOF_N, EOF_N, SOP_N, EOP_N, SRC_RDY_N, DST_RDY_N;
  endclocking: monitor_cb;

  // Receive Modport
  modport dut ( output DATA,
                output DREM,
                output SOF_N,
                output EOF_N,
                output SOP_N,
                output EOP_N,
                output SRC_RDY_N,
                input  DST_RDY_N);

  // Transitive Modport
  modport tb (clocking cb);

  // Monitor Modport
  modport monitor (clocking monitor_cb);


  // --------------------------------------------------------------------------
  // -- Interface properties/assertions
  // --------------------------------------------------------------------------

    // -- While RESET DST_RDY_N inactive ----------------------------------------
  // DST_RDY_N may be active only if RESET is inactive.

  property RESETDST;
     @(posedge CLK) (RESET)|->(DST_RDY_N);
  endproperty

  assert property (RESETDST)
     else $error("TX_DST_RDY_N is active during reset.");


  // -- SOF together with SOP -------------------------------------------------
  // SOF may be active only if SOP is active.

  property SOFSOP;
     @(posedge CLK) !(SOF_N) && !(SRC_RDY_N)|->!(SOP_N);
  endproperty

  assert property (SOFSOP)
     else $error("TX_SOF_N is not active the same time as TX_SOP_N.");


  // -- EOF together with EOP -------------------------------------------------
  // EOF may be active only if EOP is active.

  property EOFEOP;
     @(posedge CLK) !(EOF_N) && !(SRC_RDY_N)|->!(EOP_N);
  endproperty

  assert property (EOFEOP)
     else $error("TX_EOF_N is not active the same time as TX_EOP_N.");


  // -- No data after EOP ----------------------------------------------------
  // After EOP, data cannot be sent, until SOP is sent. EOP marks end of
  // transaction. First, we define a sequence of waiting for the first active
  // SOP. Then we declare, that after active cycle of EOP, there may be no
  // transfer during that sequence ( = until active SOP).

  sequence sop_seq;
     ##[0:$] (!SOP_N) && !(SRC_RDY_N || DST_RDY_N);
  endsequence

  property NoDataAfterEOP;
     @(posedge CLK) disable iff (RESET)
        (!EOP_N) && !(SRC_RDY_N || DST_RDY_N) |=>
	   !(SOP_N && !(SRC_RDY_N || DST_RDY_N)) throughout sop_seq;
  endproperty

  assert property (NoDataAfterEOP)
     else $error("FrameLink transaction continued after TX_EOP_N.");


  // -- Matching EOP after SOP ------------------------------------------------
  // Each SOP must be, after some time, followed by EOP. Each transaction must
  // have its end. First, we define a sequence of waiting for the first active
  // EOP. Then we declare, that after active cycle of SOP, there may be no
  // another active SOP during that sequence ( = until active EOP).
  sequence eop_seq;
     ##[0:$] (!EOP_N) && !(SRC_RDY_N || DST_RDY_N);
  endsequence

  property EOPMatchSOP;
     @(posedge CLK) disable iff (RESET)
        (!SOP_N) && (EOP_N) && !(SRC_RDY_N || DST_RDY_N) |=>
           (!((!SOP_N) && !(SRC_RDY_N || DST_RDY_N))) throughout eop_seq;
  endproperty

  assert property (EOPMatchSOP)
     else $error("TX_SOP_N was not followed by matching TX_EOP_N.");


  // -- Matching EOF after SOF ------------------------------------------------
  // Each SOF must be, after some time, followed by EOF. Each transaction must
  // have its end. First, we define a sequence of waiting for the first active
  // EOF. Then we declare, that after active cycle of SOF, there may be no
  // another active SOF during that sequence ( = until active EOF).
  sequence eof_seq;
     ##[0:$] (!EOF_N) && !(SRC_RDY_N || DST_RDY_N);
  endsequence

  property EOFMatchSOF;
     @(posedge CLK) disable iff (RESET)
        (!SOF_N) && (EOF_N) && !(SRC_RDY_N || DST_RDY_N) |=>
           (!((!SOF_N) && !(SRC_RDY_N || DST_RDY_N))) throughout eof_seq;
  endproperty

  assert property (EOFMatchSOF)
     else $error("TX_SOF_N was not followed by matching TX_EOF_N.");

endinterface : iFrameLinkTx
