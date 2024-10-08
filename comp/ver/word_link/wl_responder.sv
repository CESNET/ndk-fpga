/*
 * wl_responder_pkg.sv: Word Link Responder
 * Copyright (C) 2015 CESNET
 * Author(s): Lukas Kekely <kekely@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

/**
 * Word Link Responder Class.
 * This class is responsible for random intertransaction's dealys.
 * Unit must be enabled by "setEnable()" function
 * call. Random delaying can be stoped by "setDisable()" function call.
 */
class WordLinkResponder#(int pDataWidth=512);

   //! Responder identification
   string  inst;
   //! Responder is enabled
   bit     enabled;
   //! Interface pointer
   virtual iWordLinkTx.tb #(pDataWidth) dc;

   //! Enable/Disable delays between transactions
   rand bit enRxDelay;
   //! Enable delays between transaction (weight)
   int rxDelayEn_wt             = 1;
   //! Disable delays between transaction (weight)
   int rxDelayDisable_wt        = 3;
   //! Delay between transactions
   rand integer rxDelay;
   //! Min delay between transactions
   int rxDelayLow               = 0;
   //! Max delay between transactions limits
   int rxDelayHigh              = 3;

   /**
    * Constrains.
    * These constraints apply parameters to random delays generation.
    */
   constraint cDelays{
      enRxDelay dist{1'b1 := rxDelayEn_wt,
                     1'b0 := rxDelayDisable_wt};

      rxDelay inside{[rxDelayLow:rxDelayHigh]};
   }


   // -- Public Class Methods --

   /**
    * Constructor.
    * @param inst Instance name
    * @param dc Interface pointer
    */
   function new(string inst,
                virtual iWordLinkTx.tb#(pDataWidth) dc
               );
      this.enabled     = 0;           // Monitor is disabled by default
      this.dc          = dc;          // Store pointer interface
      this.inst        = inst;        // Store driver identifier

      // Setting default values for Frame Link interface
      dc.cb.DST_RDY <= 0;             // Ready ONLY IF enabled
   endfunction

   /**
    * Enable responder and run responder process.
    */
   task setEnabled();
      enabled = 1; // Responder Enabling
      fork
         run();     // Creating responder subprocess
      join_none;   // Don't wait for ending
   endtask : setEnabled

   /**
    * Disable responder.
    */
   task setDisabled();
      enabled = 0; // Disable responder, after receiving last transaction
   endtask : setDisabled

   /**
    * Run Responder.
    */
   task run();

      // Repeat while enabled
      while (enabled) begin

         // destination ready active for one cycle
         dc.cb.DST_RDY <= 1;
         @(dc.cb);

         // randomize waits
         assert(randomize());
         waitRxDelay();
      end // while

      dc.cb.DST_RDY <= 0;
   endtask : run

   /**
    * Random wait between transactions (Set DST_RDY to 0).
    */
   task waitRxDelay();
      if (enRxDelay)
         repeat (rxDelay) begin
            dc.cb.DST_RDY <= 0;
            @(dc.cb);
         end // repeat
   endtask : waitRxDelay

endclass: WordLinkResponder
