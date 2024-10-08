/*
 * mem_driver.sv: Memory Driver
 * Copyright (C) 2008 CESNET
 * Author(s): Marek Santa <xsanta06@stud.fit.vutbr.cz>
 *            Marcela Simkova <xsimko03@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 * TODO:
 *
 */
  // --------------------------------------------------------------------------
  // -- Memory Driver Class
  // --------------------------------------------------------------------------
  /* This class is responsible for generating signals to Mem2nFifo
   * interface. Transactions are received by 'transMbx'(Mailbox) property.
   * Unit must be enabled by "setEnable()" function call. Generation can be
   * stoped by "setDisable()" function call. You can send your custom
   * transaction by calling "sendTransaction" function.
   */
  class MemDriver #(int pDataWidth=64,int pFlows=8,int pBlSize=512,int pLutMem=0, pGlobSt=0, bool pFullPrint=FALSE);

    // -- Private Class Atributes --
    string    inst;                             // Driver identification
    bit       enabled;                          // Driver is enabled
    tTransMbx transMbx;                         // Transaction mailbox
    DriverCbs cbs[$];                           // Callbacks list
    virtual iNFifoTx.mem_write_tb #(pDataWidth,pFlows,pBlSize,pLutMem,pGlobSt) m_w;

    int  new_len[]  = new [pFlows];  // store NEW_LEN value for each flow
      // range of NEW_LEN values
      int new_lenlow               = 3;
      int new_lenhigh              = pBlSize;

    int  wr_addr[]  = new [pFlows];  // store actual WR_ADDR for each flow
    int  counter[]  = new [pFlows];  // store actual adress counter in the depence of new len
    int  stat[] = new [pFlows];      // store actual status for each block
    int  count[] = new [pFlows];     // store actual counter of address after release or status reach

    // ----
    rand bit enFwDelay;   // Enable/Disable delays between transactions
      // Enable/Disable delays between transaction (weights)
      int fwDelayEn_wt             = 1;
      int fwDelayDisable_wt        = 3;

    rand integer fwDelay; // Delay between transactions
      // Delay between transactions limits
      int fwDelayLow          = 0;
      int fwDelayHigh         = 3;
    // ----

    // -- Constrains --
    constraint cDelays {
      enFwDelay dist { 1'b1 := fwDelayEn_wt,
                       1'b0 := fwDelayDisable_wt
                     };

      fwDelay inside {
                      [fwDelayLow:fwDelayHigh]
                     };
      }

    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    // Create driver object
    function new ( string inst,
                   tTransMbx transMbx,
                   virtual iNFifoTx.mem_write_tb #(pDataWidth,pFlows,pBlSize,pLutMem,pGlobSt) m_w
                         );
      this.enabled     = 0;            // Driver is disabled by default
      this.m_w         = m_w;          // Store pointer interface
      this.transMbx    = transMbx;     // Store pointer to mailbox
      this.inst        = inst;         // Store driver identifier

      for (int j=0; j<pFlows;j++) begin
        this.new_len[j]=$urandom_range(new_lenhigh, new_lenlow);
        this.wr_addr[j]=0;
        this.counter[j]=0;
        this.stat[j]=0;
        this.count[j]=0;
      end

      this.m_w.mem_write_cb.DATA_IN      <= 0;
      this.m_w.mem_write_cb.BLOCK_ADDR   <= 0;
      this.m_w.mem_write_cb.WR_ADDR      <= 0;
      this.m_w.mem_write_cb.NEW_LEN      <= 0;
      this.m_w.mem_write_cb.NEW_LEN_DV   <= 0;
      this.m_w.mem_write_cb.WRITE        <= 0;
    endfunction: new

    // -- Set Callbacks -------------------------------------------------------
    // Put callback object into List
    function void setCallbacks(DriverCbs cbs);
      this.cbs.push_back(cbs);
    endfunction : setCallbacks

    // -- Enable Driver -------------------------------------------------------
    // Enable driver and runs driver process
    task setEnabled();
      enabled = 1; // Driver Enabling
      fork
        run();     // Creating driver subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled

    // -- Disable Driver ------------------------------------------------------
    // Disable generator
    task setDisabled();
      enabled = 0; // Disable driver, after sending last transaction it ends
    endtask : setDisabled

    // -- Send Transaction ----------------------------------------------------
    // Send transaction to Frame Link interface
    task sendTransaction( BufferTransaction transaction );
      Transaction tr;
      $cast(tr, transaction);

      // Call transaction preprocesing, if is available
      foreach (cbs[i]) cbs[i].pre_tx(tr, inst);

      // Wait before sending transaction
 //     if (enFwDelay) repeat (fwDelay) @(m_w.mem_write_cb);

      // Send transaction
      sendData(transaction);
      // Set not ready
      m_w.mem_write_cb.WRITE         <= 0;

      // Call transaction postprocesing, if is available
      foreach (cbs[i]) cbs[i].post_tx(tr, inst);
    endtask : sendTransaction

    // -- Private Class Methods --

    // -- Run Driver ----------------------------------------------------------
    // Take transactions from mailbox and generate them to interface
    task run();
      BufferTransaction transaction;
      Transaction to;
      @(m_w.mem_write_cb);             // Wait for clock
      while (enabled) begin            // Repeat while enabled
        if (transMbx.num()==0) markedAllOccupied();
        transMbx.get(to);              // Get transaction from mailbox
        $cast(transaction,to);
        assert(randomize());
        sendTransaction(transaction);  // Send Transaction
//        transaction.display("DRIVER");
      end
    endtask : run

    // -- Marked All Occupied -------------------------------------------------
    // Marked appropriate address space in memory as occupied for each flow
    task markedAllOccupied;
    if (pFullPrint == TRUE) begin
      $write("ZACINA SA VYPRAZDNOVAT!!!\n");
    end
    @(m_w.mem_write_cb);
      for (int i=0; i<pFlows; i++) begin
       // if (stat[i]>=pBlSize/2)
        new_len[i]=count[i];
        if (pFullPrint == TRUE) begin
          $write("blok: %d,  NEW_LEN pre vyprazdnovanie by malo byt: %d\n",i, new_len[i]);
        end
        markedOccupied(i);
        m_w.mem_write_cb.NEW_LEN <= 0;
        m_w.mem_write_cb.NEW_LEN_DV <= 0;
      end
    endtask :markedAllOccupied

    // -- Marked Occupied -----------------------------------------------------
    // Marked appropriate address space in memory as occupied
    task markedOccupied(input int block);
      bit [$clog2(pBlSize+1)*pFlows-1:0] pom=m_w.mem_write_cb.NEW_LEN;
      bit [$clog2(pBlSize+1)-1:0]addr;
      int m=0;
      int gener;
      int value1,value2;

      value1=block*$clog2(pBlSize+1);
      value2=(block+1)*$clog2(pBlSize+1);

      addr=new_len[block];

      for (int i=value1; i<value2; i++)
        pom[i] = addr[m++];

      m_w.mem_write_cb.NEW_LEN <= pom;
      m_w.mem_write_cb.NEW_LEN_DV[block]   <= 1;

      gener=$urandom_range(new_lenhigh, new_lenlow);
      if (pFullPrint == TRUE) begin
        $write("vygenerovana hodnota GENER: %d\n",gener);
      end
      if (counter[block]==0) counter[block]=new_len[block]+gener;//pocitadlo pre adresy, stara hodnota new_len +novo vygenerovana
      else counter[block]=counter[block]+gener;
      new_len[block]=gener;//do new len len nanovo vygenerovana hodnota
      @(m_w.mem_write_cb);
    endtask : markedOccupied

    task getStatus(int block);
      int value1=block*$clog2(pBlSize+1);
      int value2=(block+1)*$clog2(pBlSize+1);
      int m=0;

      stat[block]=0;

      for(int i=value1; i<value2; i++) begin
        if (m_w.mem_write_cb.STATUS_F[i]==1) stat[block]+=$pow(2,m++);
        else m++;
      end
    endtask : getStatus

    // -- Send transaction data -----------------------------------------------
    // Send transaction data
    task sendData(BufferTransaction tr);
      logic [pDataWidth-1:0] dataToSend = 0;
      int block;
      int kus;

      block = tr.num_block_addr;
      getStatus(block);

      if (pFullPrint == TRUE) begin
        $write("Block:%d Adresa: %d NewLen:%d Counter: %d Status: %d\n",block,wr_addr[block],new_len[block],counter[block],stat[block]);
      end

      // if address reaches BLOCK_SIZE then goes to null
      if (wr_addr[block]==pBlSize) begin
        wr_addr[block]=0;
        counter[block]=0;
      end
      // set signals
      m_w.mem_write_cb.WR_ADDR <= wr_addr[block]++;
      m_w.mem_write_cb.WRITE <= 1;
      m_w.mem_write_cb.BLOCK_ADDR <= block;

      for (int i=0;i<tr.data.size; i++)
        dataToSend[i]=tr.data[i];
      m_w.mem_write_cb.DATA_IN <= dataToSend;

      // incrementation of address counter
      count[block]++;
      if (pFullPrint == TRUE) begin
        $write("Count: %d\n",count[block]);
      end

    // detect status reaching
    if (count[block]+stat[block]>=(pBlSize/2)) begin
        if (pFullPrint == TRUE) begin
          $write("robi sa status clean\n");
        end
        if (stat[block]==pBlSize/2) begin
        // taking transactions away until status!=0
        do begin
          getStatus(block);
          if (pFullPrint == TRUE) begin
            $write("1block:  %d   status: %d\n",block,stat[block]);
          end
          @(m_w.mem_write_cb);
        end while (stat[block]!=0);
        // address counter starts with 1!! because one address would be lost
        //count[block]=1;
        end

        else begin
        do begin
        getStatus(block);
        if (pFullPrint == TRUE) begin
          $write("2block:  %d   status: %d\n",block,stat[block]);
        end
        @(m_w.mem_write_cb);
        end while (stat[block]!=0);

        new_len[block]=count[block];
        markedOccupied(block);
        count[block]=0;
        m_w.mem_write_cb.NEW_LEN <= 0;
        m_w.mem_write_cb.NEW_LEN_DV <= 0;
        end
    end

    // actual address == new_len, so release address space
    if(counter[block]!=0) begin
        if(wr_addr[block]==counter[block]) begin
          if (pFullPrint == TRUE) begin
            $write("PRI RELEASE: Block:%d Count:%d\n",block,count[block]);
          end
          new_len[block]=count[block];
          markedOccupied(block);
          count[block]=0;
        end
        else @(m_w.mem_write_cb);
    end
    else begin
        if(wr_addr[block]==new_len[block]) begin
          if (pFullPrint == TRUE) begin
            $write("PRI RELEASE: Block:%d Count:%d\n",block,count[block]);
          end
          new_len[block]=count[block];
          markedOccupied(block);
          count[block]=0;
        end
        else @(m_w.mem_write_cb);
    end
    // set signals
    m_w.mem_write_cb.DATA_IN <= 0;
    m_w.mem_write_cb.NEW_LEN <= 0;
    m_w.mem_write_cb.NEW_LEN_DV <= 0;
    endtask : sendData

  endclass : MemDriver

