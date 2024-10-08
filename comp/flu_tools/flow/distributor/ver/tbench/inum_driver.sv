/*
 * inum_driver.sv: FrameLinkUnaligned Driver
 * Copyright (C) 2012 CESNET
 * Author(s): Lukas Kekely <kekely@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 */

// ----------------------------------------------------------------------------
//                Control Interface declaration
// ----------------------------------------------------------------------------

// -- Control Interface ----------------------------------------
interface inumInterface #(pPorts = 4) (input logic CLK, RESET);
  // Control Interface
  logic [pPorts-1:0] INUM_MASK ;
  logic INUM_READY;
  logic INUM_NEXT;

  // Clocking blocks
  clocking cb @(posedge CLK);
    input INUM_NEXT;
    output INUM_READY, INUM_MASK;
  endclocking: cb;

  // Control Modport
  modport dut (output INUM_NEXT,
               input  INUM_READY,
               input  INUM_MASK
               );

  modport tb (clocking cb);

endinterface : inumInterface

// --------------------------------------------------------------------------
// -- INUM Driver Class
// --------------------------------------------------------------------------

class inumDriver #(int pPorts=4)
   extends Driver;

   //! Interface pointer
   virtual inumInterface.tb #(pPorts) ii;

   //! Enable/Disable delays inside transactions
   rand bit enDelay;
   //! Enable delay inside transaction weight
   int DelayEn_wt     = 1;
   //! Disable delay inside trans weight
   int DelayDisable_wt= 3;

   //! Value of delay inside transaction
   rand int Delay;
   //! Min delay inside transaction
   int DelayLow  = 0;
   //! Max delay inside transaction
   int DelayHigh = 3;

   /**
    * Constrains for randomization
    */
   constraint cDelaysPositions {
      enDelay dist { 1'b1 := DelayEn_wt,
                             1'b0 := DelayDisable_wt};

      Delay inside {[DelayLow:DelayHigh]};
   }


   // -- Public Class Methods --

   /**
    * Object constructor.
    * @param inst       Instance name
    * @param transMbx   Input mailbox for transactions
    * @param flu        Interface pointer
    */
   function new(string inst,
                tTransMbx transMbx,
                virtual inumInterface.tb #(pPorts) ii
               );

      super.new(inst, transMbx);       // Create super object

      this.enabled     = 0;            // Driver is disabled by default
      this.busy        = 0;            // Driver is not busy by default
      this.ii          = ii;           // Store pointer to interface
      this.transMbx    = transMbx;     // Store pointer to mailbox
      this.inst        = inst;         // Store driver identifier

      this.ii.cb.INUM_MASK      <= 0;
      this.ii.cb.INUM_READY     <= 0;
   endfunction: new

   /**
    * Send single transaction to inum interface.
    * @param transaction Transaction to be sent.
    */
   task sendTransaction(Transaction transaction);
      // Driver is sending transaction
      busy = 1;

      // Call transaction preprocesing, if is available
      foreach (cbs[i]) cbs[i].pre_tx(transaction, inst);

      // Wait before sending transaction
      if (enDelay) begin
         repeat (delay) @(ii.cb);
      end

      // Send transaction
      sendData(transaction);

      // Set not ready
      ii.cb.INUM_READY <= 0;

      // Call transaction postprocesing, if is available
      foreach (cbs[i]) cbs[i].post_tx(transaction, inst);

      // Driver is not sending transaction
      busy = 0;
   endtask : sendTransaction

   // -- Private Class Methods --

   /**
    * Take transactions from mailbox and send them to the interface.
    */
   task run();
      Transaction to;
      @(ii.cb);                       // Wait for clock
      while (enabled) begin            // Repeat while enabled
         assert(randomize());          // Randomize rand variables
         transMbx.get(to);             // Get transaction from mailbox
         sendTransaction(to);          // Send Transaction
         //transaction.display(inst);    // You may want to comment this
      end
   endtask : run


   /**
    * Wait for accepting of single word.
    */
   task waitForAccept();
      while (!ii.cb.INUM_NEXT) begin
         @(ii.cb);
      end;
   endtask : waitForAccept


   /**
    * Send transaction data.
    */
   task sendData(Transaction tr);
      FrameLinkUTransaction to;
      logic[pPorts-1:0] dataToSend = 0;

      $cast(to,tr);
      // Start sending
      // -- For all bytes in packet --
      for (int j=0; j < pPorts; j++) begin
        dataToSend[j]=to.data[j/8][j%8];
      end;

      ii.cb.INUM_READY <= 1;
      ii.cb.INUM_MASK <= dataToSend;
      @(ii.cb);
      waitForAccept();
   endtask : sendData

endclass : inumDriver

