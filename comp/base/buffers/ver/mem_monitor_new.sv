/*
 * mem_monitor.sv: Memory Monitor
 * Copyright (C) 2010 CESNET
 * Author(s): Marek Santa <santa@liberouter.org>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 * TODO: Delays in PIPE_EN for (!pLutMem && pOutputReg) not supported
 *
 */

  // --------------------------------------------------------------------------
  // -- Memory Monitor Class
  // --------------------------------------------------------------------------
  /* This class is responsible for creating transaction objects from
   * Fifo interface signals. After is transaction received it is sended
   * by callback to processing units (typicaly scoreboard) Unit must be enabled
   * by "setEnable()" function call. Monitoring can be stoped by "setDisable()"
   * function call.
   */
  class MemMonitorNew #(int pDataWidth=64, pFlows=2, pBlSize=512,
                        pLutMem=0, pOutputReg = 0) extends Monitor;

    // -- Private Class Atributes --
    virtual iMemRead.tb #(pDataWidth,pFlows,pBlSize) mem;

    const int pStatusSize = $clog2(pBlSize+1);
    // Status for each flow
    bit [$clog2(pBlSize+1)/*pStatusSize*/-1:0] status[pFlows] = '{default: 0};
    // Store REL_LEN for each flow
    int                   relLen[pFlows] = '{default: 0};
    // Store RD_ADDR for each FLOW
    int                   rdAddr[pFlows] = '{default: 0};
    // Count of already read items for each FLOW
    int         countOfReadItems[pFlows] = '{default: 0};
    // Don't read from currently released flow
    byte                dontRead[pFlows] = '{default: 0};

    // Cycle random block
    randc int block;
    // ----
    rand bit enReadDelay;   // Enable/Disable delays between transactions
      // Enable/Disable delays between transaction (weights)
      int readDelayEn_wt             = 1;
      int readDelayDisable_wt        = 3;

    rand bit enPipeDelay;   // Enable/Disable delays between transactions
      // Enable/Disable delays between transaction (weights)
      int pipeDelayEn_wt             = 1;
      int pipeDelayDisable_wt        = 3;
    // ----

    constraint cDelays {
      block inside {
                    [0:pFlows-1]
                   };

      enReadDelay dist { 1'b1 := readDelayEn_wt,
                         1'b0 := readDelayDisable_wt
                       };

      enPipeDelay dist { 1'b1 := pipeDelayEn_wt,
                         1'b0 := pipeDelayDisable_wt
                       };
      }

    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    function new ( string inst,
                   virtual iMemRead.tb #(pDataWidth,pFlows,pBlSize) mem
                   );
      super.new(inst);

      this.mem     = mem;     // Store pointer interface

      this.mem.cb.REL_LEN_DV <= 0;
      this.mem.cb.REL_LEN    <= 0;
      this.mem.cb.READ       <= 0;
      this.mem.cb.PIPE_EN    <= 1;

    endfunction: new

    // -- Run Monitor ---------------------------------------------------------
    // Receive transactions and send them for processing by call back
    task run();
      BufferTransaction transaction;

      @(mem.cb);

      while (enabled) begin              // Repeat in forever loop
        // Create new transaction object
        transaction = new;

        // Get flow where are still unreaded items
        while (1) begin
          assert(randomize());

          // Get and parse status
          getStatus();

          // If there are unreaded items
          if ((status[block]!=countOfReadItems[block]) && dontRead[block]==0)
            break;

          @(mem.cb);

          // Decrement counter for each flow
          decrementCounters();
        end

        // Set busy bit
        busy = 1;

        // Set address
        mem.cb.BLOCK_ADDR <= block;
        mem.cb.RD_ADDR    <= rdAddr[block];

        // Set READ and PIPE_EN signals
        if (!enReadDelay)
          mem.cb.READ    <= 1;
        if (enPipeDelay)
          mem.cb.PIPE_EN <= 0;

        // Increment read address
        if (!enReadDelay && !enPipeDelay) begin
          countOfReadItems[block]++;
          rdAddr[block] = (rdAddr[block]+1)%pBlSize;
        end

        // If all items for the flow was read, release the items
        if (status[block]==countOfReadItems[block])
          releaseBlock(block);

        @(mem.cb);
        // Receive transaction
        if (!enReadDelay && !enPipeDelay) begin
          fork
            automatic int bl = block;
            receiveBufferTr(transaction, bl);
          join_none;
        end

        // Reset signals
        mem.cb.READ       <= 0;
        mem.cb.PIPE_EN    <= 1;
        mem.cb.REL_LEN_DV <= 0;

        // Decrement counter for each flow
        decrementCounters();

        // Clear busy bit
        busy = 0;
      end
    endtask : run

    // -- Receive Transaction -------------------------------------------------
    // It receives buffer transaction to tr object
    task receiveBufferTr(BufferTransaction transaction, int flow);
      Transaction tr;

      $cast(tr, transaction);

      // Call transaction preprocesing, if is available
      foreach (cbs[i]) cbs[i].pre_rx(tr, inst);

      // Receive Data
      receiveData(transaction, flow);
//      tr.display("Monitor");

      // Necessary for not calling callback after monitor disabling
      if (!enabled) return;

      #(0); // Necessary for not calling callback before driver

      // Call transaction postprocesing, if is available
      foreach (cbs[i]) cbs[i].post_rx(tr, inst);

    endtask : receiveBufferTr

    // -- Get Status ----------------------------------------------------------
    // Get and parse status values
    task getStatus();
      for (int i=0; i < pFlows; i++) begin
        for (int j=0; j < $clog2(pBlSize+1); j++)
          status[i][j] = mem.cb.STATUS[i*$clog2(pBlSize+1)+j];
//        $write("STATUS[%0d]=%0d\n",i,status[i]);
      end
    endtask : getStatus

    // -- Decrement counters --------------------------------------------------
    // Decrement counters that was set after items releasing to avoid
    // repetitive reading for the same flow
    task decrementCounters();
      foreach (dontRead[i])
        if (dontRead[i] != 0)
          dontRead[i]--;
    endtask : decrementCounters

    // -- Release block -------------------------------------------------------
    // Release items from the block
    task releaseBlock(int block);
      setRelLen(block, status[block]);
      mem.cb.REL_LEN_DV[block] <= 1;
      // From the currently released flow is is not possible to read
      // for next two clock cycles
      dontRead[block] = 3;
      countOfReadItems[block] = 0;
    endtask : releaseBlock

    // -- Set REL_LEN ----------------------------------------------------------
    // Release items in memory for the flow
    task setRelLen(int flow, int stat);
      for (int j=0; j < $clog2(pBlSize+1); j++)
        mem.cb.REL_LEN[flow*$clog2(pBlSize+1)+j] <= status[flow][j];
    endtask : setRelLen

    // -- Receive Transaction data --------------------------------------------
    // It receives data to tr object
    task receiveData(BufferTransaction tr, int flow);
      logic [pDataWidth-1:0] dataToReceive = 0;

      // Add latency
      if (!pLutMem) @(mem.cb);
      if (pOutputReg) @(mem.cb);

      waitForDataVld();

      // Receive data
      for (int i=0; i<pDataWidth; i++)
        dataToReceive[i]=mem.cb.DATA_OUT[i];

      // --------- Store received data into transaction -------------
      tr.dataSize       = pDataWidth;
      tr.data           = new [pDataWidth];
      for (int i=0; i<pDataWidth; i++)
        tr.data[i]      = dataToReceive[i];
      tr.num_block_addr = flow;

    endtask: receiveData

    // -- Wait for DATA_VLD ---------------------------------------------------
    // Wait for DATA_VLD signal
    task waitForDataVld();
      while(mem.cb.DATA_VLD == 0)
        @(mem.cb);
    endtask : waitForDataVld

  endclass : MemMonitorNew
