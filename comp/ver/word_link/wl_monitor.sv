/*
 * wl_monitor.sv: Word Link Monitor
 * Copyright (C) 2015 CESNET
 * Author(s): Lukas Kekely <kekely@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */


/**
 * Word Link Monitor.
 * This class is responsible for creating transaction objects from
 * Word Link interface signals.
 * After the transaction is received it is sent
 * by callback to processing units (typicaly scoreboard).
 * Unit must be enabled
 * by "setEnable()" function call. Monitoring can be stoped by "setDisable()"
 * function call.
 */
class WordLinkMonitor #(int pDataWidth=512) extends Monitor;

   //! Interface pointer
   virtual iWordLinkTx.monitor #(pDataWidth) dc;

  // -- Public Class Methods --

   /**
    * Constructor.
    * @param inst Instance name
    * @param flu Receive interface
    */
   function new(string inst, virtual iWordLinkTx.monitor#(pDataWidth) dc);

      super.new(inst);              // Call super constructor

      this.enabled     = 0;         // Monitor is disabled by default
      this.busy        = 0;         // Monitor is not busy by default
      this.dc          = dc;        // Store pointer interface
      this.inst        = inst;      // Store driver identifier

   endfunction

   /**
    * Run Monitor.
    * Receive transactions and send them for processing by callback.
    */
   task run();
      WordLinkTransaction transaction;
      Transaction tr;

      //$write($time, " Monitor_run start.\n");

      while (enabled) begin              // Repeat in forewer loop
         transaction = new;               // Create new transaction object
         $cast(tr, transaction);

         // Call transaction preprocesing, if is available
         foreach (cbs[i]) cbs[i].pre_rx(tr, inst);

         // Receive Transaction
         receiveTransaction(transaction); // Receive Transaction

         // Necessary for not calling callback after monitor disabling
         if (!enabled) break;

         //$write($time, " :\n");
         //transaction.display(inst);

         #(0); // Necessary for not calling callback before driver

         // Call transaction postprocesing, if is available
         foreach (cbs[i]) cbs[i].post_rx(tr, inst);

         // Monitor received transaction and is not busy
         busy = 0;
      end
      //$write($time, " Monitor_run end.\n");
   endtask : run

   /**
    * Wait for DST_RDY and SRC_RDY.
    */
   task waitForDstRdy();
      do begin
         if ((!dc.monitor_cb.DST_RDY) || (!dc.monitor_cb.SRC_RDY))
            @(dc.monitor_cb);
      //Detect Destination Ready
      end while ((!dc.monitor_cb.DST_RDY) || (!dc.monitor_cb.SRC_RDY));
  endtask : waitForDstRdy

   /**
    * Receive Word Link transaction to tr object.
    * @param transaction Output transaction.
    */
   task receiveTransaction(WordLinkTransaction transaction);

      waitForDstRdy();

      // Get data word byte by byte
      transaction.data = new [(pDataWidth-1)/8+1];
      for (int i = 0; i < transaction.data.size; i++) begin
         transaction.data[i] = dc.monitor_cb.DATA[8*i +: 8];
      end;  // for

      @(dc.monitor_cb);

   endtask : receiveTransaction

endclass : WordLinkMonitor
