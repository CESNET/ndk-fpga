/*
 * wl_driver.sv: FrameLinkUnaligned Driver
 * Copyright (C) 2015 CESNET
 * Author(s): Lukas Kekely <kekely@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */


/**
 * Word Link Driver.
 * This class is responsible for generating signals to Word Link
 * interface. Transactions are received by 'transMbx'(Mailbox) property.
 * Unit must be enabled by "setEnable()" function call. Generation can be
 * stoped by "setDisable()" function call. You can send your custom
 * transaction by calling "sendTransaction" function.
 */
class WordLinkDriver #(int pDataWidth=512)
   extends Driver;

   //! Interface pointer
   virtual iWordLinkRx.tb #(pDataWidth) dc;

   //! Semaphore to solve problems with subprocesses
   semaphore sem;

   //! Enable/Disable delays
   rand bit enTxDelay;
   //! Enable delay weight
   int txDelayEn_wt     = 1;
   //! Disable delay weight
   int txDelayDisable_wt= 3;

   //! Value of delay
   rand int txDelay;
   //! Min delay
   int txDelayLow  = 0;
   //! Max delay
   int txDelayHigh = 3;

   /**
    * Constrains for randomization
    */
   constraint cDelaysPositions {
      enTxDelay dist { 1'b1 := txDelayEn_wt,
                       1'b0 := txDelayDisable_wt};

      txDelay inside {[txDelayLow:txDelayHigh]};
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
                virtual iWordLinkRx.tb #(pDataWidth) dc
               );

      super.new(inst, transMbx);       // Create super object
      this.sem = new(1);               // Create semaphore

      this.enabled     = 0;            // Driver is disabled by default
      this.busy        = 0;            // Driver is not busy by default
      this.dc          = dc;           // Store pointer to interface
      this.transMbx    = transMbx;     // Store pointer to mailbox
      this.inst        = inst;         // Store driver identifier

      this.dc.cb.DATA      <= 0;
      this.dc.cb.SRC_RDY   <= 0;
   endfunction: new

   /**
    * Lock driver
    */
   function int tryLock();
      return sem.try_get(1);          // Try set semaphore to lock
   endfunction: tryLock

   /**
    * Lock driver
    */
   task lock();
      sem.get(1);                     // Semaphore is set to lock
   endtask: lock

   /**
    * Unlock driver
    */
   task unlock();
      sem.put(1);                     // Semaphore is set to unlock
   endtask: unlock

   /**
    * Send single transaction to interface.
    * @param transaction Transaction to be sent.
    */
   task sendTransaction(WordLinkTransaction transaction);
      Transaction tr;
      $cast(tr, transaction);

      // Lock driver
      lock();

      // Driver is sending transaction
      busy = 1;

      // Call transaction preprocesing, if is available
      foreach (cbs[i]) cbs[i].pre_tx(tr, inst);

      // Send transaction
      sendData(transaction);

      // Set not ready
      dc.cb.SRC_RDY <= 0;

      // Call transaction postprocesing, if is available
      foreach (cbs[i]) cbs[i].post_tx(tr, inst);

      // Driver is not sending transaction
      busy = 0;

      // Unlock driver
      unlock();
   endtask : sendTransaction

   // -- Private Class Methods --

   /**
    * Take transactions from mailbox and send them to the interface.
    */
   task run();
      WordLinkTransaction transaction;
      Transaction to;
      time before_get;

      @(dc.cb);                        // Wait for clock

      while (enabled) begin            // Repeat while enabled
         assert(randomize());          // Randomize rand variables
         before_get = $time;
         transMbx.get(to);             // Get transaction from mailbox
         if($time != before_get)       // Get can take some time, therefore, clock block synchronization can be lost and must be restored
           @(dc.cb);
         $cast(transaction,to);
         sendTransaction(transaction); // Send Transaction
         //transaction.display(inst);    // You may want to comment this
      end
   endtask : run


   /**
    * Wait for accepting of single word.
    */
   task waitForAccept();
      while (!dc.cb.DST_RDY) begin
         @(dc.cb);
      end;
   endtask : waitForAccept

   /**
    * Random wait during sending transaction (Set SRC_RDY to 0).
    */
   task randomWait();
      if (enTxDelay) begin
         repeat (txDelay) begin
            dc.cb.SRC_RDY <= 0;
            @(dc.cb); // Wait for send
         end
      end; // if
      dc.cb.SRC_RDY <= 1;
      assert(randomize());
   endtask : randomWait


   /**
    * Send transaction data.
    */
   task sendData(WordLinkTransaction tr);
      logic[pDataWidth-1:0] dataToSend = 0;
      randomWait();
      for (int j=0; j < tr.data.size; j++) begin
         dataToSend[j*8 +: 8] = tr.data[j];
      end;
      dc.cb.DATA    <= dataToSend;
      @(dc.cb);
      waitForAccept();
   endtask : sendData

endclass : WordLinkDriver

