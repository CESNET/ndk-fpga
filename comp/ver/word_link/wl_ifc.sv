/*
 * wl_ifc.pkg: Word Link Interface
 * Copyright (C) 2015 CESNET
 * Author(s): Lukas Kekely <kekely@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */


/**
 * Word Link RX Interface.
 * @param CLK Clock
 * @param RESET Synchronous reset
 */
interface iWordLinkRx #(DWIDTH=512) (input logic CLK, RESET);
   logic [DWIDTH-1:0] DATA      = 0; // Data
   logic SRC_RDY                = 0; // Source data ready
   logic DST_RDY;                    // Destination data ready


   clocking cb @(posedge CLK);
      input  DST_RDY;
      output DATA, SRC_RDY;
   endclocking: cb;

   //! Receive Modport
   modport dut (input  DATA,
                input  SRC_RDY,
                output DST_RDY);

   //! Transitive Modport
   modport tb (clocking cb);


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

endinterface : iWordLinkRx



/**
 * WordLink TX Interface.
 * @param CLK Clock
 * @param RESET Synchronous reset
 */
interface iWordLinkTx #(DWIDTH=512) (input logic CLK, RESET);
   logic [DWIDTH-1:0] DATA;       // Data
   logic SRC_RDY;                 // Source data ready
   logic DST_RDY = 0;             // Destination data ready


   clocking cb @(posedge CLK);
      output  DST_RDY;
      input DATA, SRC_RDY;
   endclocking: cb;

   clocking monitor_cb @(posedge CLK);
      input DATA, SRC_RDY, DST_RDY;
   endclocking: monitor_cb;

   // Receive Modport
   modport dut ( output DATA,
                 output SRC_RDY,
                 input  DST_RDY);

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

endinterface : iWordLinkTx



/**
 * WordLink Probe Interface.
 * @param CLK Clock
 * @param RESET Synchronous reset
 */
interface iWordLinkProbe #(DWIDTH=512) (input logic CLK, RESET);
   logic [DWIDTH-1:0] DATA;       // Data
   logic SRC_RDY;                 // Source data ready
   logic DST_RDY;                 // Destination data ready


   clocking monitor_cb @(posedge CLK);
      input DATA, SRC_RDY, DST_RDY;
   endclocking: monitor_cb;

   // Passive DUT Output Modport
   modport dut ( output DATA,
                 output SRC_RDY,
                 output DST_RDY);

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

endinterface : iWordLinkProbe
