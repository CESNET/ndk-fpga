/*
 * fl_monitor_pkg.sv: FrameLink Monitor
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


  // --------------------------------------------------------------------------
  // -- Frame Link Monitor Class
  // --------------------------------------------------------------------------
  /* This class is responsible for creating transaction objects from
   * Frame Link interface signals. After is transaction received it is sended
   * by callback to processing units (typicaly scoreboard) Unit must be enabled
   * by "setEnable()" function call. Monitoring can be stoped by "setDisable()"
   * function call.
   */
  class FrameLinkMonitor #(int pDataWidth=32, int pDremWidth=2);

    // -- Private Class Atributes --
    string  inst;                          // Monitor identification
    bit     enabled;                       // Monitor is enabled
    bit     busy;                          // Monitor is receiving transaction
    MonitorCbs cbs[$];                     // Callbacks list
    virtual iFrameLinkTx#(pDataWidth,pDremWidth).monitor fl;

    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    function new ( string inst,
                   virtual iFrameLinkTx#(pDataWidth,pDremWidth).monitor fl
                   );
      this.enabled     = 0;           // Monitor is disabled by default
      this.busy        = 0;           // Monitor is not busy by default
      this.fl          = fl;          // Store pointer interface
      this.inst        = inst;        // Store driver identifier

    endfunction

    // -- Set Callbacks -------------------------------------------------------
    // Put callback object into List
    function void setCallbacks(MonitorCbs cbs);
      this.cbs.push_back(cbs);
    endfunction : setCallbacks

    // -- Enable Monitor ------------------------------------------------------
    // Enable monitor and runs monitor process
    task setEnabled();
      enabled = 1; // Monitor Enabling
      fork
        run();     // Creating monitor subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled

    // -- Disable Monitor -----------------------------------------------------
    // Disable monitor
    task setDisabled();
      enabled = 0; // Disable monitor, after receiving last transaction
    endtask : setDisabled

    // -- Run Monitor ---------------------------------------------------------
    // Receive transactions and send them for processing by call back
    task run();
      FrameLinkTransaction transaction;
      Transaction tr;

      while (enabled) begin              // Repeat in forewer loop
        transaction = new;               // Create new transaction object
        $cast(tr, transaction);

        // Call transaction preprocesing, if is available
        foreach (cbs[i]) cbs[i].pre_rx(tr, inst);

        // Receive Transaction
        receiveTransaction(transaction); // Receive Transaction
//        transaction.display(inst);

        // Necessary for not calling callback after monitor disabling
        if (!enabled) break;

        #(0); // Necessary for not calling callback before driver

        // Call transaction postprocesing, if is available
        foreach (cbs[i]) cbs[i].post_rx(tr, inst);

        // Monitor received transaction and is not busy
        busy = 0;
      end
    endtask : run

    // -- Wait for SOF --------------------------------------------------------
    // It waits until SOF and SRC_RDY
    task waitForSOF();
      do begin
        // Wait if not data ready
        if (fl.monitor_cb.SOF_N || fl.monitor_cb.SRC_RDY_N || fl.monitor_cb.DST_RDY_N)
          @(fl.monitor_cb);
        if (!enabled) return;
      end while (fl.monitor_cb.SOF_N || fl.monitor_cb.SRC_RDY_N || fl.monitor_cb.DST_RDY_N); //Detect Start of Frame
    endtask : waitForSOF

    // -- Wait for SOP --------------------------------------------------------
    // It waits until SOP and SRC_RDY
    task waitForSOP();
      do begin
        if (fl.monitor_cb.SOP_N || fl.monitor_cb.SRC_RDY_N || fl.monitor_cb.DST_RDY_N)
          @(fl.monitor_cb);
      end while (fl.monitor_cb.SOP_N || fl.monitor_cb.SRC_RDY_N || fl.monitor_cb.DST_RDY_N); //Detect Start of Packet
    endtask : waitForSOP

    // -- Wait for DST_RDY ----------------------------------------------------
    // It waits until DST_RDY and SRC_RDY
    task waitForDstRdy();
      do begin
        if (fl.monitor_cb.DST_RDY_N || fl.monitor_cb.SRC_RDY_N)
          @(fl.monitor_cb);
      end while (fl.monitor_cb.DST_RDY_N || fl.monitor_cb.SRC_RDY_N); //Detect Destination Ready
    endtask : waitForDstRdy

    // -- Receive Transaction -------------------------------------------------
    // It receives Frame Link transaction to tr object
    task receiveTransaction(FrameLinkTransaction tr);
      int packet_no=0;
      int removeBytes;
      byte unsigned aux[];

      waitForSOF(); // Wait for SOF

      // Monitor receives transaction
      busy = 1;

      // -------- Process Packets -----------
      do begin
        waitForSOP();               // Wait for SOP

        // -------- Process data in packet -----------
        do begin
          waitForDstRdy();

          // Get data word
          aux = new[aux.size + pDataWidth/8](aux);
          aux[aux.size-1 -: pDataWidth/8] = {<< byte{fl.monitor_cb.DATA}};

          if (fl.monitor_cb.EOP_N || fl.monitor_cb.SRC_RDY_N)
            @(fl.monitor_cb);
          else
            break;           // Detect End of Packet
        end while (1);

        // Remove invalid bytes from last data word
        removeBytes = pDataWidth/8 - 1 - fl.monitor_cb.DREM;
        aux = new[aux.size - removeBytes](aux);

        // --------- Store received data into transaction -------------
        tr.packetCount = packet_no+1;
        tr.data = new [tr.packetCount](tr.data);
        tr.data[tr.data.size-1] = new [aux.size];
        tr.data[tr.packetCount-1] = aux;
        aux.delete();


        if (fl.monitor_cb.EOF_N || fl.monitor_cb.SRC_RDY_N) begin
          @(fl.monitor_cb);
          packet_no++;
        end
        else break;                                 // Detect End of Frame

      end while (1);

      @(fl.monitor_cb);

    endtask : receiveTransaction

  endclass : FrameLinkMonitor
