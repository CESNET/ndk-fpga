/*
 * length_driver.sv: Control Interface Driver
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
interface lengthInterface #(width = 12) (input logic CLK, RESET);
  // Control Interface
  logic [width-1:0] LENGTH ;
  logic LENGTH_READY;
  logic LENGTH_NEXT;

  // Clocking blocks
  clocking cb @(posedge CLK);
    input LENGTH_NEXT;
    output LENGTH_READY, LENGTH;
  endclocking: cb;

  // Control Modport
  modport dut (output LENGTH_NEXT,
               input  LENGTH_READY,
               input  LENGTH
               );

  modport tb (clocking cb);

endinterface : lengthInterface

// --------------------------------------------------------------------------
// -- LENGTH Driver Class
// --------------------------------------------------------------------------

class lengthDriver #(int width=12)
   extends Driver;

   //! Interface pointer
   virtual lengthInterface.tb #(width) ii;

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
                virtual lengthInterface.tb #(width) ii
               );

      super.new(inst, transMbx);       // Create super object

      this.enabled     = 0;            // Driver is disabled by default
      this.busy        = 0;            // Driver is not busy by default
      this.ii          = ii;           // Store pointer to interface
      this.transMbx    = transMbx;     // Store pointer to mailbox
      this.inst        = inst;         // Store driver identifier

      this.ii.cb.LENGTH           <= 0;
      this.ii.cb.LENGTH_READY     <= 0;
   endfunction: new

   /**
    * Send single transaction to interface.
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
      ii.cb.LENGTH_READY <= 0;

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
      while (!ii.cb.LENGTH_NEXT) begin
         @(ii.cb);
      end;
   endtask : waitForAccept


   /**
    * Send transaction data.
    */
   task sendData(Transaction tr);
      FrameLinkUTransaction to;
      int x;
      logic[width-1:0] dataToSend = 0;

      $cast(to,tr);
      // Start sending
      // -- For all bytes in packet --
      x=to.data[0];                    //normal behaviour!!
      if(x<10) begin // all ones
        for (int j=0; j < width; j++) begin
          dataToSend[j]=1;
        end;
      end
      else if (x>180) begin // all zeros
        for (int j=0; j < width; j++) begin
          dataToSend[j]=0;
        end;
      end
      else  // trimm length
        for (int j=0; j < width; j++) begin
          dataToSend[j]=to.data[j/8][j%8];
        end;
      /*if(to.data[0]>200) x=1; else x=0;  // only zeros or ones (allow/discard, no trim)
      for (int j=0; j<width; j++) begin
        dataToSend[j]=x;
      end;*/

      ii.cb.LENGTH_READY <= 1;
      ii.cb.LENGTH       <= dataToSend;
      @(ii.cb);
      waitForAccept();
   endtask : sendData

endclass : lengthDriver

