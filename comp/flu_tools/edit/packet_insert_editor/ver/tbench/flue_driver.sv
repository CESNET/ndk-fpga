/*
 * flue_driver.sv: FrameLinkUnaligned (+ Edit interface) Driver
 * Copyright (C) 2015 CESNET
 * Author(s): Pavel Benacek <benacek@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 */

import sv_common_pkg::*;

// --------------------------------------------------------------------------
// -- FrameLinkUnaligned with Edit interface Driver Class
// --------------------------------------------------------------------------
/**
 * FrameLinkUnaligned with Edit interface Driver.
 * This class is responsible for generating signals to FrameLinkUnaligned
 * (+ Edit) interface. Transactions are received by 'transMbx'(Mailbox) property.
 * Unit must be enabled by "setEnable()" function call. Generation can be
 * stoped by "setDisable()" function call. You can send your custom
 * transaction by calling "sendTransaction" function.
 */
class FrameLinkUEditDriver #(int pDataWidth=512, int pEopWidth=6, int pSopWidth=3,int pOffsetWidth = 10)
   extends Driver;

   // Private Class Atributes
   //! Last value of eop_pos
   int       last_eop_pos;
   //! Last transaction has finished
   bit       finished;
   //! Interface pointer
   virtual iFrameLinkUEditRx.tb #(pDataWidth,pEopWidth,pSopWidth,pOffsetWidth) flu;
   //! Covers some special cases
   bit       oneword_transaction = 0;

   //! Semaphore to solve problems with subprocesses
   semaphore sem;

   //! Enable/Disable delays inside transactions
   rand bit enInsideTxDelay;
   //! Enable delay inside transaction weight
   int insideTxDelayEn_wt     = 1;
   //! Disable delay inside trans weight
   int insideTxDelayDisable_wt= 3;

   //! Value of delay inside transaction
   rand int insideTxDelay;
   //! Min delay inside transaction
   int insideTxDelayLow  = 0;
   //! Max delay inside transaction
   int insideTxDelayHigh = 3;

   //! Position of the SOP
   rand int startPosition;
   //! Min value of sop_pos
   int startPositionLow  = 0;
   //! Max value of sop_pos
   int startPositionHigh = (2**pSopWidth)-1;

   /**
    * Constrains for randomization
    */
   constraint cDelaysPositions {
      enInsideTxDelay dist { 1'b1 := insideTxDelayEn_wt,
                             1'b0 := insideTxDelayDisable_wt};

      insideTxDelay inside {[insideTxDelayLow:insideTxDelayHigh]};

      // What user wanted
      startPosition inside {[startPositionLow:startPositionHigh]};
      // What makes sense
      startPosition inside {[startPositionLow:(2**pSopWidth)-1]};
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
                virtual iFrameLinkUEditRx.tb #(pDataWidth,pEopWidth,pSopWidth,pOffsetWidth) flu
               );

      super.new(inst, transMbx);       // Create super object
      this.sem = new(1);               // Create semaphore

      this.enabled     = 0;            // Driver is disabled by default
      this.busy        = 0;            // Driver is not busy by default
      this.flu         = flu;          // Store pointer to interface
      this.transMbx    = transMbx;     // Store pointer to mailbox
      this.inst        = inst;         // Store driver identifier
      this.last_eop_pos= 0;            // Set EOP_POS of the previous trans.
      this.finished    = 1;            // Set state of the the last trans.

      this.flu.cb.DATA         <= 0;
      this.flu.cb.EOP_POS      <= 0;
      this.flu.cb.SOP_POS      <= 0;
      this.flu.cb.SOP          <= 0;
      this.flu.cb.EOP          <= 0;
      this.flu.cb.SRC_RDY      <= 0;
      this.flu.cb.OFFSET       <= 0;
      this.flu.cb.EN_INSERT    <= 0;
      this.flu.cb.EN_REPLACE   <= 0;
      this.flu.cb.NEW_DATA     <= 0;
      this.flu.cb.MASK         <= 0;
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
    * Send single transaction to FrameLinkUnaligned interface.
    * @param transaction Transaction to be sent.
    */
   task sendTransaction(FrameLinkUEditTransaction transaction);
      Transaction tr;
      $cast(tr, transaction);

      // Lock driver
      lock();

      // Driver is sending transaction
      busy = 1;

      // Call transaction preprocesing, if is available
      foreach (cbs[i]) cbs[i].pre_tx(tr, inst);

      // Wait before sending transaction
      if (enInsideTxDelay) begin
        repeat (insideTxDelay) @(flu.cb);
      end

      // Send transaction
      sendData(transaction);

      // Set not ready
      flu.cb.SRC_RDY <= 0;

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
      FrameLinkUEditTransaction transaction;
      Transaction to;
      time before_get;

      @(flu.cb);                       // Wait for clock

      while (enabled) begin            // Repeat while enabled
         assert(randomize());          // Randomize rand variables
         before_get = $time;
         transMbx.get(to);             // Get transaction from mailbox
         if($time != before_get)       // Get can take some time, therefore, clock block synchronization can be lost and must be restored
           @(flu.cb);
         $cast(transaction,to);
         sendTransaction(transaction); // Send Transaction
         //transaction.display(inst);    // You may want to comment this
      end
   endtask : run


   /**
    * Wait for accepting of single word.
    */
   task waitForAccept();
      while (!flu.cb.DST_RDY) begin
         @(flu.cb);
      end;
   endtask : waitForAccept

   /**
    * Immediately finish the transaction by sending its last word.
    */
   task finishTransaction();
      if (!finished) begin
         flu.cb.SRC_RDY <= 1;
         @(flu.cb);         // Send data
         waitForAccept();  // Wait until opposite side sets ready
         // Init for sending next data word
         flu.cb.SRC_RDY <= 0;
         flu.cb.EOP <= 0;
         finished = 1;
      end;
   endtask : finishTransaction

   /**
    * Finish the transaction some time in the future.
    * (For the random delay of the last word.)
    */
   task delayedFinishTransaction();
      if (enInsideTxDelay) begin
         repeat (insideTxDelay) begin
            @(flu.cb);
         end;
      end;

      if (tryLock()) begin
         finishTransaction();
         unlock();
      end;
   endtask : delayedFinishTransaction

   /**
    * Random wait during sending transaction (Set SRC_RDY to 0).
    * @param whole If 0, only delay-related rand variables are randomized.
    * If 1, also the startPosition variable is randomized. Only after the
    * whole transaction was already sent.
    */
   task randomWait(bit whole);
      if (enInsideTxDelay) begin
         repeat (insideTxDelay) begin
            flu.cb.SRC_RDY <= 0;
            @(flu.cb); // Wait for send
         end
      end; // if

      flu.cb.SRC_RDY <= 1;

      if (!whole)
         // Disable randomization of this variable
         // It can change only between transactions
         startPosition.rand_mode(0);
      assert(randomize());     // Randomize variables for next randomWait
      startPosition.rand_mode(1); // Enable randomization again
   endtask : randomWait


   /**
    * Send transaction data.
    */
   task sendData(FrameLinkUEditTransaction tr);
      logic[31:0] newDataToSend = 0;
      logic[pDataWidth-1:0] dataToSend = 0;
      int j,k;
      bit lastword;
      // Width of one SOP_POS step (bits)
      int sopstep = pDataWidth/(2**pSopWidth);
      int m = sopstep*startPosition;
      int firstm = m;

      // Check if we can add to the current FLU word. We can NOT if:
      //    If it simply overlaps OR
      //    if it would end in the first word (only one EOP is in FLU protocol)
      //    OR previous transaction had only one word (only one SOP in proto)
      if (last_eop_pos >= startPosition*sopstep/8 ||
          (startPosition*sopstep/8 + tr.data.size) <= pDataWidth/8 ||
          oneword_transaction) begin
         if(last_eop_pos != -1) // case when end of last packet is aligned
            finishTransaction(); // wait only when nonaligned
      end;

      // Mark this transaction unfinished
      finished = 0;

      // Prepare data for edit interface and send data via FLU interface
      flu.cb.OFFSET       <= tr.offset;
      flu.cb.EN_INSERT    <= tr.insertData;
      flu.cb.EN_REPLACE   <= tr.editData;
      flu.cb.MASK         <= tr.mask;

      // Prepare new Data to send
      for(int j=0;j < 4;j++)
        newDataToSend[j*8 +: 8] = tr.newData[j];

      flu.cb.NEW_DATA     <= newDataToSend;

      // Start sending
      // -- For all bytes in packet --
      for (int j=0; j < tr.data.size; j++) begin

         if (j==0) begin
            flu.cb.SOP <= 1;                  //Set Start of Packet
            flu.cb.SOP_POS <= startPosition;
         end;

         // Set one Data Byte
         dataToSend[m +: 8] = tr.data[j];
         m += 8;

         // Last Byte in Packet
         lastword = 0;
         if (j==tr.data.size-1) begin          //Last byte of packet
            lastword = 1;
            flu.cb.EOP <= 1;                   //Set End Of Packet
            // Set EOP_POS signal
            last_eop_pos = ((tr.data.size+sopstep*startPosition/8)
                            %(pDataWidth/8))-1;
            flu.cb.EOP_POS <= last_eop_pos;
            flu.cb.DATA <= dataToSend;
            if ((startPosition*sopstep/8 + tr.data.size) <= pDataWidth/8)
               oneword_transaction = 1;
            else
               oneword_transaction = 0;

            // Schedule the transaction to be finished later
            fork
               delayedFinishTransaction();
            join_none; // No wait
         end

         // When data word is ready to be sent
         if (m==pDataWidth) begin
            for (int i=pDataWidth-1; i >= firstm; i--)
               flu.cb.DATA[i] <= dataToSend[i];
            randomWait(lastword);     // Wait before sending the word
            @(flu.cb);
            waitForAccept();
            dataToSend = 0;
            flu.cb.SOP <= 0;
            flu.cb.EOP <= 0;
            m = 0;
            firstm = 0;
         end
      end // for
   endtask : sendData

endclass : FrameLinkUEditDriver

