/*
 * fl_fifo_ctrl_checker.sv: FrameLink FIFO Control Interface Checker
 * Copyright (C) 2008 CESNET
 * Author(s): Marek Santa <xsanta06@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 * TODO:
 *
 */

  import math_pkg::*;
  // --------------------------------------------------------------------------
  // -- Frame Link FIFO Checker Class
  // --------------------------------------------------------------------------
  /* This class is responsible for checking correct setting of Control Interface
   * signals. Unit must be enabled by "setEnable()" function call. Monitoring
   * can be stoped by "setDisable()" function call.
   */
  class FrameLinkFifoChecker #(int pDataWidth=32, pDremWidth=2, pBlockSize=16,
                               pStatusWidth=8, pItems=512, pUseBrams=0);

    // -- Private Class Atributes --
    string  inst;                            // Checker identification
    bit     enabled;                         // Checker is enabled
    virtual iFrameLinkRx.tb #(pDataWidth,pDremWidth) rx;
    virtual iFrameLinkTx.tb #(pDataWidth,pDremWidth) tx;
    virtual iFrameLinkFifo.ctrl_tb #(pStatusWidth)   ctrl;

    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    function new ( string inst,
                   virtual iFrameLinkRx.tb #(pDataWidth,pDremWidth) rx,
                   virtual iFrameLinkTx.tb #(pDataWidth,pDremWidth) tx,
                   virtual iFrameLinkFifo.ctrl_tb #(pStatusWidth)   ctrl
                   );
      this.enabled     = 0;           // Monitor is disabled by default
      this.rx          = rx;          // Store pointer RX interface
      this.tx          = tx;          // Store pointer TX interface
      this.ctrl        = ctrl;        // Store pointer CTRL interface
      this.inst        = inst;        // Store driver identifier

    endfunction

    // -- Enable Checker ------------------------------------------------------
    // Enable checker and runs checkers process
    task setEnabled();
      enabled = 1; // Checker Enabling
      fork
        run();     // Creating checker subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled

    // -- Disable Checker -----------------------------------------------------
    // Disable checker
    task setDisabled();
      enabled = 0; // Disable checker
    endtask : setDisabled

    // -- Run Checker ---------------------------------------------------------
    // Check correstness of Control Interface signals
    task run();
      int items = 0;                     // Items allready stored in fifo
      int frames = 0;                    // Frames allready stored in fifo
      while (enabled) begin              // Repeat in forewer loop
        updateStatus(items, frames);     // Update Control ifc signals
        @(ctrl.ctrl_cb);
        if (pUseBrams) checkStatusBRAM(items, frames);    // Check Control ifc signals
        else checkStatusSRAM(items, frames);
      end
    endtask : run

    // -- Update Status -------------------------------------------------------
    // Update status according to Rx and Tx interfaces
    // Counts stored items and frames
    task updateStatus(inout int items, frames);
      if (!rx.cb.SRC_RDY_N && !rx.cb.DST_RDY_N) begin
        items++;
        if (!rx.cb.EOF_N) frames++;
      end
      if (!tx.cb.SRC_RDY_N && !tx.cb.DST_RDY_N) begin
        items--;
        if (!tx.cb.SOF_N) frames--;
        end
    endtask : updateStatus

    // -- Check Status SRAM ---------------------------------------------------
    // Compare expected status with signals on Control Interface
    // (SelectiveRAM used)
    task checkStatusSRAM(int items, frames);
      // MSBs of exact number of free items in the fifo
      logic [pStatusWidth-1:0] status = (pItems-items)>>(log2(pItems)+1-pStatusWidth);

      // LSTBLK assertion
      assert (((pItems-items<=pBlockSize) && ctrl.ctrl_cb.LSTBLK) ||
              ((pItems-items>pBlockSize) && !ctrl.ctrl_cb.LSTBLK))
      else $error("Error: Wrong LSTBLK signal\n");

      // STATUS assertion
      assert (status==ctrl.ctrl_cb.STATUS)
      else $error("Error: Wrong STATUS signal\n");

      // EMPTY assertion
      assert (((items==0) && ctrl.ctrl_cb.EMPTY) ||
              ((items!=0) && !ctrl.ctrl_cb.EMPTY))
      else $error("Error: Wrong EMPTY signal\n");

      // FULL assertion
      assert (((items==pItems) && ctrl.ctrl_cb.FULL) ||
              ((items!=pItems) && !ctrl.ctrl_cb.FULL))
      else $error("Error: Wrong FULL signal\n");

      // FRAME_RDY assertion
      assert (((frames<=0) && !ctrl.ctrl_cb.FRAME_RDY) ||
            ((frames>0) && ctrl.ctrl_cb.FRAME_RDY))
      else $error("Error: Wrong FRAME_RDY signal\n");

    endtask : checkStatusSRAM

    // -- Check Status BRAM ---------------------------------------------------
    // Compare expected status with signals on Control Interface
    // (BlockRAM used)
    // Because of output pipelining, signals LSTBLK, STATUS, EMPTY and FULL may
    // be inaccurate by one or two items.
    task checkStatusBRAM(int items, frames);
      // MSBs of exact number of free items in the fifo
      logic [pStatusWidth-1:0] status0 = (pItems-items)>>(log2(pItems)+1-pStatusWidth);
      logic [pStatusWidth-1:0] status1 = (pItems-items+1)>>(log2(pItems)+1-pStatusWidth);
      logic [pStatusWidth-1:0] status2 = (pItems-items+2)>>(log2(pItems)+1-pStatusWidth);

      // LSTBLK assertion
      assert (((pItems-items<=pBlockSize || pItems-items+1<=pBlockSize || pItems-items+2<=pBlockSize) && ctrl.ctrl_cb.LSTBLK) ||
              ((pItems-items>pBlockSize || pItems-items+1>pBlockSize || pItems-items+2>pBlockSize) && !ctrl.ctrl_cb.LSTBLK))
      else $error("Error: Wrong LSTBLK signal\n");

      // STATUS assertion
      assert (status0==ctrl.ctrl_cb.STATUS || status1==ctrl.ctrl_cb.STATUS ||
              status2==ctrl.ctrl_cb.STATUS)
      else $error("Error: Wrong STATUS signal\n");

      // EMPTY assertion
      assert (((items==0 || items==1 || items==2) && ctrl.ctrl_cb.EMPTY) ||
              ((items!=0 || items!=1 || items!=2) && !ctrl.ctrl_cb.EMPTY))
      else $error("Error: Wrong EMPTY signal\n");

      // FULL assertion
      assert (((items==pItems || items-1==pItems || items-2==pItems) && ctrl.ctrl_cb.FULL) ||
              ((items!=pItems || items-1!=pItems || items-2!=pItems) && !ctrl.ctrl_cb.FULL))
      else $error("Error: Wrong FULL signal\n");

      // FRAME_RDY assertion
      assert (((frames<=0) && !ctrl.ctrl_cb.FRAME_RDY) ||
            ((frames>0) && ctrl.ctrl_cb.FRAME_RDY))
      else $error("Error: Wrong FRAME_RDY signal\n");

    endtask : checkStatusBRAM

endclass : FrameLinkFifoChecker
