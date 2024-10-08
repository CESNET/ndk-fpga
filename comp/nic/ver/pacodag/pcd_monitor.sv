/**
 * \file pcd_monitor.sv
 * \brief PACODAG Statistics Monitor
 * \author Jan Kučera <xkucer73@stud.fit.vutbr.cz>
 * \date 2014
 */

/**
 * Copyright (C) 2014 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 */

/**
 * PACODAG Statistics Monitor Class
 */
class PacodagStatsMonitor #(int pDataWidth = 64) extends Monitor;

   // -- Private Class Atributes --

   //! Interface pointer
   virtual iPacodag.monitor #(pDataWidth) pcd;

   // -- Public Class Methods --

   /**
    * Constructor.
    * @param inst Instance name
    * @param pcd PACODAG interface
    */
   function new(string inst, virtual iPacodag.monitor #(pDataWidth) pcd);
      super.new(inst);              // Call super constructor
      this.enabled     = 0;         // Monitor is disabled by default
      this.busy        = 0;         // Monitor is not busy by default
      this.pcd         = pcd;       // Store pointer interface
      this.inst        = inst;      // Store driver identifier
   endfunction

   /**
    * Run Monitor.
    * Receive transactions and send them for processing by callback.
    */
   task run();

      // Repeat while enabled
      while (enabled) begin

         // Wait for event
         while (pcd.monitor_cb.STAT_DV == 0) begin
            @(pcd.monitor_cb);
         end

         // Monitor receives transaction
         busy = 1;

         // Receive Transaction
         receiveTransaction();

         // Monitor received transaction and is not busy
         busy = 0;
      end
   endtask: run

   /**
    * Receive PACODAG statistics transaction
    * @param transaction Output transaction.
    */
   task receiveTransaction();
      PacodagStatsTransaction transaction;
      Transaction tr;

      // Create new transaction object
      transaction = new;
      $cast(tr, transaction);

      // Call transaction preprocesing, if is available
      foreach (cbs[i]) cbs[i].pre_rx(tr, inst);

      // Fill transaction data
      transaction.frameErr = pcd.monitor_cb.STAT_FRAME_ERR;
      transaction.macErr = pcd.monitor_cb.STAT_MAC_ERR;
      transaction.mintuErr = pcd.monitor_cb.STAT_MINTU_ERR;
      transaction.mtuErr = pcd.monitor_cb.STAT_MTU_ERR;
      transaction.crcErr = pcd.monitor_cb.STAT_CRC_ERR;
      transaction.frameLen = pcd.monitor_cb.STAT_FRAME_LEN;

      // Necessary for not calling callback after monitor disabling
      if (!enabled) return;

      #(0); // Necessary for not calling callback before driver

      // Call transaction postprocesing, if is available
      foreach (cbs[i]) cbs[i].post_rx(tr, inst);

      @(pcd.monitor_cb);
   endtask: receiveTransaction

endclass: PacodagStatsMonitor
