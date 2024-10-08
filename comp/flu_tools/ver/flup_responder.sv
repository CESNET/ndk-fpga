/*
 * flup_responder.sv: FrameLinkUnaligned Plus Responder
 * Copyright (C) 2015 CESNET
 * Author(s): Jan Kucera <jan.kucera@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 */

/**
 * FrameLinkUnaligned Plus Responder Class.
 * This class is responsible for random intra- and intertransaction's dealys.
 * Unit must be enabled by "setEnable()" function
 * call. Random delaying can be stoped by "setDisable()" function call.
 */
class FrameLinkUPResponder#(int pDataWidth=512,int pEopWidth=6,int pSopWidth=3, int pHdrWidth=128, int pChanWidth=4);

   //! Responder identification
   string  inst;
   //! Responder is enabled
   bit     enabled;
   //! Interface pointer
   virtual iFrameLinkUPTx#(pDataWidth,pEopWidth,pSopWidth,pHdrWidth,pChanWidth).tb flu;

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


   //! Enable/Disable delays inside transaction
   rand bit enInsideRxDelay;
   //! Enable delays inside transaction weight
   int insideRxDelayEn_wt       = 1;
   //! Disable delays inside transaction weight
   int insideRxDelayDisable_wt  = 3;
   //! Delay inside transaction
   rand integer insideRxDelay;
   //! Minimal delay between transaction words
   int insideRxDelayLow         = 0;
   //! Maximal delay between transaction words
   int insideRxDelayHigh        = 3;

   /**
    * Constrains.
    * These constraints apply parameters to random delays generation.
    */
   constraint cDelays{
      enRxDelay dist{1'b1 := rxDelayEn_wt,
                     1'b0 := rxDelayDisable_wt};

      rxDelay inside{[rxDelayLow:rxDelayHigh]};

      enInsideRxDelay dist{1'b1 := insideRxDelayEn_wt,
                           1'b0 := insideRxDelayDisable_wt};

      insideRxDelay inside{[insideRxDelayLow:insideRxDelayHigh]};
   }


   // -- Public Class Methods --

   /**
    * Constructor.
    * @param inst Instance name
    * @param flu Interface pointer
    */
   function new(string inst,
                virtual iFrameLinkUPTx#(pDataWidth,pEopWidth,pSopWidth,pHdrWidth,pChanWidth).tb flu
               );
      this.enabled     = 0;           // Monitor is disabled by default
      this.flu         = flu;         // Store pointer interface
      this.inst        = inst;        // Store driver identifier

      // Setting default values for Frame Link interface
      flu.cb.DST_RDY <= 0;            // Ready ONLY IF enabled
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
         flu.cb.DST_RDY <= 1;
         @(flu.cb);

         // randomize waits
         assert(randomize());

         if (flu.cb.EOP == 1 && flu.cb.SRC_RDY == 1)   // delay between frames
            waitRxDelay();
         else                                            // delay inside frame
            waitInsideRxDelay();
      end // while

      flu.cb.DST_RDY <= 0;
   endtask : run

   /**
    * Random wait between transactions (Set DST_RDY to 0).
    */
   task waitRxDelay();
      if (enRxDelay)
         repeat (rxDelay) begin
            flu.cb.DST_RDY <= 0;
            @(flu.cb);
         end // repeat
   endtask : waitRxDelay

   /**
    * Random wait during transaction (Set DST_RDY to 0).
    */
   task waitInsideRxDelay();
      if (enInsideRxDelay)
         repeat (insideRxDelay) begin
            flu.cb.DST_RDY <= 0;
            @(flu.cb);
         end
   endtask : waitInsideRxDelay

endclass: FrameLinkUPResponder
