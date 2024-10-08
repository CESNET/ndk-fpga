/**
 * \file flup_ifc.sv
 * \brief FrameLink Unaligned Plus Interface
 * \author Jan Kučera <xkucer73@stud.fit.vutbr.cz>
 * \date 2015
 */

/**
 * Copyright (C) 2015 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 */

/**
 * FrameLinkUnaligned Plus RX Interface.
 * @param CLK Clock
 * @param RESET Synchronous reset
 */
interface iFrameLinkUPRx #(DWIDTH=512, EOPWIDTH=6, SOPWIDTH=3, HWIDTH=128, CHWIDTH=4) (input logic CLK, RESET);
   logic [DWIDTH-1:0] DATA      = 0; // Data
   logic [HWIDTH-1:0] HEADER    = 0; // Header
   logic [CHWIDTH-1:0] CHANNEL  = 0; // Channel
   logic [SOPWIDTH-1:0] SOP_POS = 0; // First data pointer
   logic [EOPWIDTH-1:0] EOP_POS = 0; // Last data byte pointer
   logic SOP                    = 0; // Start of Packet
   logic EOP                    = 0; // End of Packet
   logic SRC_RDY                = 0; // Source data ready
   logic DST_RDY;                    // Destination data ready

   clocking cb @(posedge CLK);
      input DST_RDY;
      output DATA, HEADER, CHANNEL, SOP_POS, EOP_POS, SOP, EOP, SRC_RDY;
   endclocking: cb;

   clocking monitor_cb @(posedge CLK);
      input DATA, HEADER, CHANNEL, SOP_POS, EOP_POS, SOP, EOP, SRC_RDY, DST_RDY;
   endclocking: monitor_cb;

   //! Receive Modport
   modport dut (
		input DATA,
		input HEADER,
		input CHANNEL,
      input SOP_POS,
      input EOP_POS,
      input SOP,
      input EOP,
      input SRC_RDY,
      output DST_RDY
	);

   //! Transitive Modport
   modport tb (clocking cb);

   //! Monitor Modport
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

endinterface : iFrameLinkUPRx



/**
 * FrameLinkUnaligned Plus TX Interface.
 * @param CLK Clock
 * @param RESET Synchronous reset
 */
interface iFrameLinkUPTx #(DWIDTH=512, EOP_WIDTH=6, SOP_WIDTH=3, HWIDTH=128, CHWIDTH=4) (input logic CLK, RESET);
   logic [DWIDTH-1:0] DATA;       // Data
   logic [HWIDTH-1:0] HEADER;     // Header
   logic [CHWIDTH-1:0] CHANNEL;   // Channel
   logic [SOP_WIDTH-1:0] SOP_POS; // First data pointer
   logic [EOP_WIDTH-1:0] EOP_POS; // Last data byte pointer
   logic SOP;                     // Start of Packet
   logic EOP;                     // End of Packet
   logic SRC_RDY;                 // Source data ready
   logic DST_RDY = 0;             // Destination data ready


   clocking cb @(posedge CLK);
      output DST_RDY;
      input DATA, HEADER, CHANNEL, SOP_POS, EOP_POS, SOP, EOP, SRC_RDY;
   endclocking: cb;

   clocking monitor_cb @(posedge CLK);
      input DATA, HEADER, CHANNEL, SOP_POS, EOP_POS, SOP, EOP, SRC_RDY, DST_RDY;
   endclocking: monitor_cb;

   // Receive Modport
   modport dut (
		output DATA,
		output HEADER,
		output CHANNEL,
      output SOP_POS,
      output EOP_POS,
      output SOP,
      output EOP,
      output SRC_RDY,
      input DST_RDY
	);

   // Transitive Modport
   modport tb (clocking cb);

   // Monitor Modport
   modport monitor (clocking monitor_cb);


   // --------------------------------------------------------------------------
   // -- Interface properties/assertions
   // --------------------------------------------------------------------------

   // -- While RESET DST_RDY inactive ----------------------------------------
   // DST_RDY_N may be active only if RESET is inactive.

   property RESETDST;
      @(posedge CLK) (RESET)|->(!DST_RDY);
   endproperty

   assert property (RESETDST)
      else $error("DST_RDY is active during reset.");


   // -- No data after EOP ----------------------------------------------------
   // After EOP, data cannot be sent, until SOP is sent. EOP marks end of
   // transaction. First, we define a sequence of waiting for the first active
   // SOP. Then we declare, that after active cycle of EOP without SOP or with
   // SOP_POS <= EOP_POS, there may be no transfer during that sequence
   // (= until active SOP).

   sequence sop_seq;
      ##[0:$] (SOP) && !(!SRC_RDY || !DST_RDY);
   endsequence

   property NoDataAfterEOP;
      @(posedge CLK) disable iff (RESET)
         (EOP) && (!SOP || SOP_POS*2**(EOP_WIDTH-SOP_WIDTH) <= EOP_POS) && (SRC_RDY && DST_RDY) |=>
	    !(!SOP && (SRC_RDY && DST_RDY)) throughout sop_seq;
   endproperty

   assert property (NoDataAfterEOP)
      else $error("FrameLinkUnaligned transaction continued after TX_EOP.");


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
         (SOP) && (!EOP || SOP_POS*2**(EOP_WIDTH-SOP_WIDTH) > EOP_POS) && (SRC_RDY && DST_RDY) |=>
       !(((SOP && !EOP) || (SOP && EOP && SOP_POS*2**(EOP_WIDTH-SOP_WIDTH) <= EOP_POS)) && (SRC_RDY && DST_RDY)) throughout eop_seq;
   endproperty

   assert property (EOPMatchSOP)
      else $error("TX_SOP was not followed by matching TX_EOP.");

endinterface : iFrameLinkUPTx
