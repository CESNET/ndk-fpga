/*
 * fifo_monitor.sv: Fifo Monitor
 * Copyright (C) 2008 CESNET
 * Author(s): Marcela Simkova <xsimko03@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 * TODO:
 *
 */


  // --------------------------------------------------------------------------
  // -- Fifo Monitor Class
  // --------------------------------------------------------------------------
  /* This class is responsible for creating transaction objects from
   * Fifo interface signals. After is transaction received it is sended
   * by callback to processing units (typicaly scoreboard) Unit must be enabled
   * by "setEnable()" function call. Monitoring can be stoped by "setDisable()"
   * function call.
   */
  class nFifoMonitor #(int pDataWidth=64,int pFlows=2,int pBlSize=512,int pLutMem=0, pGlobSt=0);

    // -- Private Class Atributes --
    string  inst;                            // Monitor identification
    int     ifcNo;                           // Number of connected interface
    bit     enabled;                         // Monitor is enabled
    MonitorCbs cbs[$];                       // Callbacks list
    virtual iNFifoTx.nfifo_monitor #(pDataWidth,pFlows,pBlSize,pLutMem,pGlobSt) monitor;

    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    function new ( string inst,
                   int ifcNo,
                   virtual iNFifoTx.nfifo_monitor #(pDataWidth,pFlows,pBlSize,pLutMem,pGlobSt) monitor
                   );
      this.enabled     = 0;           // Monitor is disabled by default
      this.monitor     = monitor;     // Store pointer interface
      this.inst        = inst;        // Store driver identifier
      this.ifcNo       = ifcNo;       // Store number of connected interface

    endfunction: new

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
      BufferTransaction transaction;
      Transaction tr;
      while (enabled) begin              // Repeat in forewer loop
        transaction = new;               // Create new transaction object
        receiveTransaction(transaction); // Receive Transaction
        #(0); // Necessary for not calling callback before driver
        if (enabled) begin
          $cast(tr, transaction);
          // Call transaction preprocesing, if is available
          foreach (cbs[i]) cbs[i].pre_rx(tr, inst);
          // Call transaction postprocesing, if is available
          foreach (cbs[i]) cbs[i].post_rx(tr, inst);
        end
      end
    endtask : run

    // -- Wait for DATA_VLD ----------------------------------------------------
    // It waits until DATA_VLD and READ
    task waitForDataVld(); // Cekej dokud neni DATA_VLD a READ
      do begin
        if (!monitor.nfifo_monitor_cb.DATA_VLD || !monitor.nfifo_monitor_cb.READ) begin
          @(monitor.nfifo_monitor_cb);
          end
      end while (!monitor.nfifo_monitor_cb.DATA_VLD || !monitor.nfifo_monitor_cb.READ); //Detect Data Valid
    endtask : waitForDataVld


    // -- Receive Transaction -------------------------------------------------
    // It receives buffer transaction to tr object
    task receiveTransaction(BufferTransaction tr);
      integer flowSize = pDataWidth/pFlows;
      logic [pDataWidth-1:0] dataToReceive = 0;
      integer m=0;

      waitForDataVld();

      // Store data from interface
      for (integer i=0; i<pFlows; i++) begin
        waitForDataVld();
        for (integer j=0; j<flowSize; j++)
          dataToReceive[m++]= monitor.nfifo_monitor_cb.DATA_OUT[j];
        @(monitor.nfifo_monitor_cb);
      end


    // --------- Store received data into transaction -------------

      tr.dataSize       = pDataWidth;
      tr.data           = new [pDataWidth];
      for (int i=0; i<pDataWidth; i++)
        tr.data[i]        = dataToReceive[i];
      tr.num_block_addr = ifcNo;


    endtask : receiveTransaction

  endclass : nFifoMonitor
