/*
 * flu_ifc.pkg: FrameLink Unaligned (+Edit) Interface
 * Copyright (C) 2015 CESNET
 * Author(s): Pavel Benacek <benacek@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 */


/**
 * FrameLinkUnaligned RX Interface With Edit interface.
 * @param CLK Clock
 * @param RESET Synchronous reset
 */
interface iFrameLinkUEditRx #(DWIDTH=512, EOPWIDTH=6, SOPWIDTH=3, OFFSET_WIDTH=10) (input logic CLK, RESET);
   // FLU Interface
   logic [DWIDTH-1:0] DATA      = 0; // Data
   logic [SOPWIDTH-1:0] SOP_POS = 0; // First data pointer
   logic [EOPWIDTH-1:0] EOP_POS = 0; // Last data byte pointer
   logic SOP                    = 0; // Start of Packet
   logic EOP                    = 0; // End of Packet
   logic SRC_RDY                = 0; // Source data ready
   logic DST_RDY;                    // Destination data ready

   // Edit interface
   logic [OFFSET_WIDTH-1:0] OFFSET  = 0;    // Offset

   clocking cb @(posedge CLK);
      input DST_RDY;
      output DATA, SOP_POS, EOP_POS, SOP, EOP, SRC_RDY, OFFSET;
   endclocking: cb;

   clocking monitor_cb @(posedge CLK);
      input DATA, SOP_POS, EOP_POS, SOP, EOP, SRC_RDY, DST_RDY, OFFSET;
   endclocking: monitor_cb;

   //! Receive Modport
   modport dut (input  DATA,
                input  SOP_POS,
                input  EOP_POS,
                input  SOP,
                input  EOP,
                input  SRC_RDY,
                output DST_RDY,
                input  OFFSET);

   //! Transitive Modport
   modport tb (clocking cb);

   // Monitor Modport
   modport monitor (clocking monitor_cb);

   // --------------------------------------------------------------------------
   // -- Interface properties/assertions
   // --------------------------------------------------------------------------

   // -- While RESET SRC_RDY inactive ----------------------------------------
   // SRC_RDY may be active only if RESET is inactive.

   property RESETSRC;
      @(posedge CLK) (RESET)|->(!SRC_RDY);
   endproperty

   assert property (RESETSRC)
      else $error("SRC_RDY is active during reset.");


   // -- No data after EOP ----------------------------------------------------
   // After EOP, data cannot be sent, until SOP is sent. EOP marks end of
   // transaction. First, we define a sequence of waiting for the first active
   // SOP. Then we declare, that after active cycle of EOP without SOP or with
   // SOP_POS <= EOP_POS, there may be no transfer during that sequence
   // (= until active SOP).

   sequence sop_seq;
      ##[0:$] (SOP) && (SRC_RDY && DST_RDY);
   endsequence

   property NoDataAfterEOP;
      @(posedge CLK) disable iff (RESET)
         (EOP) && (!SOP || SOP_POS*2**(EOPWIDTH-SOPWIDTH) <= EOP_POS) && (SRC_RDY && DST_RDY) |=>
	    !(!SOP && (SRC_RDY && DST_RDY)) throughout sop_seq;
   endproperty

   assert property (NoDataAfterEOP)
      else $error("FrameLinkUnaligned transaction continued after RX_EOP.");


   // -- Matching EOP after SOP ------------------------------------------------
   // Each SOP must be, after some time, followed by EOP. Each transaction must
   // have its end. First, we define a sequence of waiting for the first active
   // EOP. Then we declare, that after active cycle of SOP, there may be no
   // another active SOP during that sequence ( = until active EOP).

   sequence eop_seq;
      ##[0:$] (EOP) && (SRC_RDY && DST_RDY);
   endsequence

   property EOPMatchSOP;
      @(posedge CLK) disable iff (RESET)
         (SOP) && (!EOP || SOP_POS*2**(EOPWIDTH-SOPWIDTH) > EOP_POS) && (SRC_RDY && DST_RDY) |=>
       !(((SOP && !EOP) || (SOP && EOP && SOP_POS*2**(EOPWIDTH-SOPWIDTH) <= EOP_POS)) && (SRC_RDY && DST_RDY)) throughout eop_seq;
   endproperty

   assert property (EOPMatchSOP)
      else $error("RX_SOP was not followed by matching RX_EOP.");

endinterface : iFrameLinkUEditRx
