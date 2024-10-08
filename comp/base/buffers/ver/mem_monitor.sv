/*
 * mem_monitor.sv: Memory Monitor
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
  // -- Memory Monitor Class
  // --------------------------------------------------------------------------
  /* This class is responsible for creating transaction objects from
   * Fifo interface signals. After is transaction received it is sended
   * by callback to processing units (typicaly scoreboard) Unit must be enabled
   * by "setEnable()" function call. Monitoring can be stoped by "setDisable()"
   * function call.
   */
  class MemMonitor #(int pDataWidth=64, pFlows=2, pBlSize=512,
                     pLutMem=0, pGlobSt=0, pOutputReg = 0);

    // -- Private Class Atributes --
    string  inst;                            // Monitor identification
    bit     enabled;                         // Monitor is enabled
    MonitorCbs cbs[$];                       // Callbacks list
    int     blockQue[$];                     // Block address queue
    virtual iNFifoRx.mem_monitor #(pDataWidth,pFlows,pBlSize,pLutMem,pGlobSt) monitor;

    int rel_len[] = new [pFlows];            // Store REL_LEN for each FLOW
    int rd_addr[] = new [pFlows];            // Store RD_ADDR for each FLOW
    int already_rel[] = new [pFlows];        // Store count of already released items for each FLOW

    mailbox #(int) dontRead;

    randc int block;                         // Cycle random block

    constraint cDelays {
      block inside {
                    [0:pFlows-1]
                   };
      }

    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    function new ( string inst,
                   virtual iNFifoRx.mem_monitor #(pDataWidth,pFlows,pBlSize,pLutMem,pGlobSt) monitor,
                   mailbox #(int) dontRead
                   );
      this.enabled     = 0;           // Monitor is disabled by default
      this.monitor     = monitor;     // Store pointer interface
      this.inst        = inst;        // Store driver identifier
      this.dontRead    = dontRead;

      for (int j=0; j<pFlows;j++) begin  // Initiate RD_ADDR and count of already released items
        this.already_rel[j]=0;
        this.rd_addr[j]=0;
      end

      this.monitor.mem_monitor_cb.REL_LEN_DV <= 0;
      this.monitor.mem_monitor_cb.REL_LEN <= 0;

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
        setBlockAddr();  // Creating subprocess for generating BLOCK_ADDR
        getBlockAddr();  // Creating subprocess for queuing BLOCK_ADDR
        run();           // Creating monitor subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled

    // -- Disable Monitor -----------------------------------------------------
    // Disable monitor
    task setDisabled();
      enabled = 0; // Disable monitor, after receiving last transaction
    endtask : setDisabled

    // -- Set Block Addr ------------------------------------------------------
    // Set BLOCK_ADDR and appropriate RD_ADDR
    task setBlockAddr();
      while (enabled) begin
        assert(randomize);
        if (pFlows!=1)           // do not random the same BLOCK_ADDR twice in row
          while (monitor.mem_monitor_cb.BLOCK_ADDR==block) block = $urandom_range(pFlows-1);

        monitor.mem_monitor_cb.BLOCK_ADDR <= block;            // Set BLOCK_ADDR
        monitor.mem_monitor_cb.RD_ADDR    <= rd_addr[block];   // Set RD_ADDR
        @(monitor.mem_monitor_cb);
      end
    endtask : setBlockAddr

    // -- Get Block Addr ------------------------------------------------------
    task getBlockAddr();
      int blockAddr, rdAddr;

      while (enabled) begin
        if (monitor.mem_monitor_cb.EMPTY[monitor.mem_monitor_cb.BLOCK_ADDR]) begin
          @(monitor.mem_monitor_cb);
          continue;
        end

        if (pLutMem && !pOutputReg)
          if (monitor.mem_monitor_cb.READ) begin
            blockAddr = monitor.mem_monitor_cb.BLOCK_ADDR;
            rdAddr    = monitor.mem_monitor_cb.RD_ADDR;
            rd_addr[blockAddr]++;
            if (rd_addr[blockAddr]==pBlSize) rd_addr[blockAddr]=0;
            blockQue.push_back(blockAddr);
            blockQue.push_back(++rdAddr);
//            $write("PUSH %x\n", monitor.mem_monitor_cb.DATA_OUT);
            @(monitor.mem_monitor_cb);
          end
          else @(monitor.mem_monitor_cb);
        else begin
          if (monitor.mem_monitor_cb.READ && monitor.mem_monitor_cb.PIPE_EN) begin
            blockAddr = monitor.mem_monitor_cb.BLOCK_ADDR;
            rdAddr    = monitor.mem_monitor_cb.RD_ADDR;
            rd_addr[blockAddr]++;
            if (rd_addr[blockAddr]==pBlSize) rd_addr[blockAddr]=0;
            if (rd_addr[blockAddr] == already_rel[blockAddr]%pBlSize) begin
              dontRead.put(1);
              $write("DontREAD was set\n");
              $write("Block:%1d Rd:%1d\n",blockAddr,rd_addr[blockAddr]);
              //releaseAllItems(blockAddr, rd_addr[blockAddr]);

            end
            @(monitor.mem_monitor_cb);
            dontRead.put(0);
            blockQue.push_back(blockAddr);
            blockQue.push_back(++rdAddr);
          end
          else @(monitor.mem_monitor_cb);
        end
      end

    endtask : getBlockAddr

    // -- Run Monitor ---------------------------------------------------------
    // Receive transactions and send them for processing by call back
    task run();
      BufferTransaction transaction;
      Transaction tr;
      while (enabled) begin              // Repeat in forewer loop
        transaction = new;               // Create new transaction object
        receiveTransaction(transaction); // Receive Transaction
//        transaction.display("Monitor / run");
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

    // -- Wait for DATA_VLD  --------------------------------------------------
    // It waits until DATA_VLD and READ
    task waitForDataVld();
      while (!monitor.mem_monitor_cb.DATA_VLD) @(monitor.mem_monitor_cb);
    endtask : waitForDataVld

    // -- Release Items -------------------------------------------------------
    // It releases items in appropriate block
    task releaseItems(int blockAddr, rdAddr);
      int value1=blockAddr*$clog2(pBlSize+1);      // Borders of STATUS belonging to input block
      int value2=(blockAddr+1)*$clog2(pBlSize+1);
      bit [$clog2(pBlSize+1)*pFlows-1:0]pom = 0;

      for(int i=value1; i<value2; i++)begin
        if (monitor.mem_monitor_cb.STATUS[i]==1) pom[i] = 1;  // Get STATUS of input block
      end

      monitor.mem_monitor_cb.REL_LEN <= pom;             // Set REL_LEN
      monitor.mem_monitor_cb.REL_LEN_DV <= 0;
      monitor.mem_monitor_cb.REL_LEN_DV[blockAddr] <= 1;     // Set REL_LEN_DV

      already_rel[blockAddr]=rdAddr;                // Store count of already released items
      if (pFlows==1) begin
        @(monitor.mem_monitor_cb);
        monitor.mem_monitor_cb.REL_LEN_DV <= 0;
        end
    endtask: releaseItems

    // -- Release All Items ---------------------------------------------------
    // It releases all items in appropriate block
    task releaseAllItems(int blockAddr, rdAddr);

      monitor.mem_monitor_cb.REL_LEN <= pBlSize << $clog2(pBlSize+1)*blockAddr;           // Set REL_LEN
      monitor.mem_monitor_cb.REL_LEN_DV <= 0;
      monitor.mem_monitor_cb.REL_LEN_DV[blockAddr] <= 1;     // Set REL_LEN_DV
      //dontRelease = 1;

      already_rel[blockAddr]=rdAddr;                // Store count of already released items
      if (pFlows==1) begin
        @(monitor.mem_monitor_cb);
        monitor.mem_monitor_cb.REL_LEN_DV <= 0;
        end
    endtask: releaseAllItems

    // -- Get REL_LEN ---------------------------------------------------------
    // It gets REL_LEN from STATUS
    task getRelLen(int blockAddr);
      int value1=blockAddr*$clog2(pBlSize+1);        // Borders of STATUS belonging to input block
      int value2=(blockAddr+1)*$clog2(pBlSize+1);
      int m=0;
      rel_len[blockAddr]=0;

      for(int i=value1; i<value2; i++) begin
        if (monitor.mem_monitor_cb.STATUS[i]==1) rel_len[blockAddr]+=$pow(2,m);   // Set REL_LEN to Status
        m++;
        end

    endtask : getRelLen


    // -- Receive Transaction data --------------------------------------------
    // It receives data to tr object
    task receiveData(BufferTransaction tr);
      logic [pDataWidth-1:0] dataToReceive = 0;
      int blockAddr = blockQue.pop_front();
      int rdAddr    = blockQue.pop_front();

//      monitor.mem_monitor_cb.REL_LEN_DV <= 0;

      waitForDataVld();

      getRelLen(blockAddr);            // Get REL_LEN from STATUS

      for (int i=0; i<pDataWidth; i++)
        dataToReceive[i]=monitor.mem_monitor_cb.DATA_OUT[i];   // Recerive data

      // --------- Store received data into transaction -------------
      tr.dataSize       = pDataWidth;
      tr.data           = new [pDataWidth];
      for (int i=0; i<pDataWidth; i++)
        tr.data[i]      = dataToReceive[i];
      tr.num_block_addr = blockAddr;

      $write("block : %1d\n",blockAddr);
      $write("rel_len+already_rel==rd_addr : %1d+%1d==%1d\n",rel_len[blockAddr],already_rel[blockAddr],rdAddr);

      // Check for release items from memory
      if ((rel_len[blockAddr]+already_rel[blockAddr])%pBlSize==rdAddr)
      begin
        $write("release\n");
        releaseItems(blockAddr, rdAddr);    // Release memory
      end

      @(monitor.mem_monitor_cb);

    endtask: receiveData


    // -- Receive Transaction -------------------------------------------------
    // It receives buffer transaction to tr object
    task receiveTransaction(BufferTransaction tr);
      monitor.mem_monitor_cb.REL_LEN_DV <= 0;
      while (!blockQue.size()) @(monitor.mem_monitor_cb);
//      $write("POP %x\n", monitor.mem_monitor_cb.DATA_OUT);
      receiveData(tr);

    endtask : receiveTransaction

  endclass : MemMonitor
