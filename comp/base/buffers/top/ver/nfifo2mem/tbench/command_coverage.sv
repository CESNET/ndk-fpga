/*
 * command_coverage: nFifo2Mem Coverage class - transaction coverage
 * Copyright (C) 2008 CESNET
 * Author(s): Marcela Simková <xsimko03@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 * TODO:
 *
 */


  // --------------------------------------------------------------------------
  // -- Fifo Command Coverage for Interface iNFifoRx.nfifo_write_cb
  // --------------------------------------------------------------------------
  // This class measures exercised combinations of interface signals

  class CommandsCoverageWrite #(int pDataWidth=64,int pFlows=8,int pBlSize=512,int pLutMem=0, pGlobSt=0);

    // Interface on witch is covering measured
    virtual iNFifoRx.nfifo_write_tb #(pDataWidth,pFlows,pBlSize,pLutMem,pGlobSt) f_w;
    string  instanceName;

    // Sampling is enabled
    bit enabled;

    // Sampled values from interface
    logic write;
    logic full;

    //-- Covering transactions ----------------------------------------------
    covergroup CommandsCovergroup;

      // write coverpoint
      write: coverpoint write {
        bins write0 = {0};
        bins write1 = {1};
      }

      // full coverpoint
      full: coverpoint full{
        bins full0 = {0};
        bins full1 = {1};
      }

      cross write, full;

      option.per_instance=1; // Also per instance statistics
     endgroup

    // ------------------------------------------------------------------------
    // Constructor

    function new (virtual iNFifoRx.nfifo_write_tb #(pDataWidth,pFlows,pBlSize,pLutMem,pGlobSt) f_w,
                  string instanceName);
      this.f_w = f_w;                 // Store interface
      CommandsCovergroup = new;       // Create covergroup
      enabled=0;                      // Disable interface sampling
      this.instanceName = instanceName;
    endfunction

    // -- Enable command coverage measures ------------------------------------
    // Enable commands coverage measures
    task setEnabled();
      enabled = 1; // Coverage Enabling
      fork
         run();    // Creating coverage subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled

    // -- Disable command coverage measures -----------------------------------
    // Disable generator
    task setDisabled();
      enabled = 0; // Disable measures
    endtask : setDisabled

    // -- Run command coverage measures ---------------------------------------
    // Take transactions from mailbox and generate them to interface
    task run();
       while (enabled) begin            // Repeat while enabled
         @(f_w.nfifo_write_cb);          // Wait for clock
         // Sample signals values
         write      = f_w.nfifo_write_cb.WRITE;
         full       = f_w.nfifo_write_cb.FULL;

         CommandsCovergroup.sample();
      end
    endtask : run

    // ------------------------------------------------------------------------
    // Display coverage statistic
    task display();
       $write("Commands coverage for %s: %d percent\n",
               instanceName, CommandsCovergroup.get_inst_coverage());
    endtask : display

  endclass: CommandsCoverageWrite

  // --------------------------------------------------------------------------
  // -- Memory Command Coverage for Interface iMemRead.tb
  // --------------------------------------------------------------------------
  // This class measures exercised combinations of interface signals

  class CommandsCoverageMonitor #(int pDataWidth=64,int pFlows=8,int pBlSize=512);

    // Interface on witch is covering measured
    virtual iMemRead.tb #(pDataWidth,pFlows,pBlSize) m_m;
    string  instanceName;

    // Sampling is enabled
    bit enabled;

    // Sampled values from interface
    logic data_vld;
    logic read;
    logic [$clog2(pFlows)-1:0] block_addr;
    logic [$clog2(pBlSize)-1:0] rd_addr;
    logic [$clog2(pBlSize+1)*pFlows-1:0] rel_len;
    logic [pFlows-1:0] rel_len_dv;
    logic pipe_en;
    logic [pFlows-1:0] empty;


    //-- Covering transactions ----------------------------------------------
    covergroup CommandsCovergroup;
      // data_vld coverpoint
      data_vld: coverpoint data_vld {
        bins data_vld0 = {0};
        bins data_vld1 = {1};
      }

      // read coverpoint
      read: coverpoint read {
        bins read0 = {0};
        bins read1 = {1};
      }

      // block_addr coverpoint
      block_addr: coverpoint block_addr;

      // rd_addr coverpoint
      rd_addr: coverpoint rd_addr;

      // rel_len coverpoint
      rel_len: coverpoint rel_len;

      // rel_len_dv coverpoint
      rel_len_dv: coverpoint rel_len_dv{
        option.auto_bin_max = pFlows;
      }

      // pipe_en coverpoint
      pipe_en: coverpoint pipe_en {
        bins pipe_en0 = {0};
        bins pipe_en1 = {1};
      }

      // empty coverpoint
      empty: coverpoint empty{
        option.auto_bin_max = pFlows;
      }

      option.per_instance=1; // Also per instance statistics
     endgroup

    // ------------------------------------------------------------------------
    // Constructor

    function new (virtual iMemRead.tb #(pDataWidth,pFlows,pBlSize) m_m,
                  string instanceName);
      this.m_m = m_m;                 // Store interface
      CommandsCovergroup = new;       // Create covergroup
      enabled=0;                      // Disable interface sampling
      this.instanceName = instanceName;
    endfunction

    // -- Enable command coverage measures ------------------------------------
    // Enable commands coverage measures
    task setEnabled();
      enabled = 1; // Coverage Enabling
      fork
         run();    // Creating coverage subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled

    // -- Disable command coverage measures -----------------------------------
    // Disable generator
    task setDisabled();
      enabled = 0; // Disable measures
    endtask : setDisabled

    // -- Run command coverage measures ---------------------------------------
    // Take transactions from mailbox and generate them to interface
    task run();
       while (enabled) begin            // Repeat while enabled
         @(m_m.cb);                    // Wait for clock
         // Sample signals values
         data_vld   = m_m.cb.DATA_VLD;
         read       = m_m.cb.READ;
         block_addr = m_m.cb.BLOCK_ADDR;
         rd_addr    = m_m.cb.RD_ADDR;
         rel_len    = m_m.cb.REL_LEN;
         rel_len_dv = m_m.cb.REL_LEN_DV;
         pipe_en    = m_m.cb.PIPE_EN;
         empty      = m_m.cb.EMPTY;


         CommandsCovergroup.sample();
      end
    endtask : run

    // ------------------------------------------------------------------------
    // Display coverage statistic
    task display();
       $write("Commands coverage for %s: %d percent\n",
               instanceName, CommandsCovergroup.get_inst_coverage());
    endtask : display

  endclass: CommandsCoverageMonitor

  // --------------------------------------------------------------------------
  // -- nFifo2Mem Coverage
  // --------------------------------------------------------------------------
  // This class measure coverage of commands
  class Coverage #(int pDataWidth=64,int pFlows=8,int pBlSize=512,int pLutMem=0, pGlobSt=0);
    // Commands coverage lists
    CommandsCoverageWrite   #(pDataWidth,pFlows,pBlSize,pLutMem,pGlobSt) cmdListWrite[$];
    CommandsCoverageMonitor #(pDataWidth,pFlows,pBlSize)                 cmdListMonitor[$];

    // -- Add interface Write for command coverage ----------------------------------
    task addGeneralInterfaceWrite (virtual iNFifoRx.nfifo_write_tb #(pDataWidth,pFlows,pBlSize,pLutMem,pGlobSt) port,
                                   string name);
      // Create commands coverage class
      CommandsCoverageWrite #(pDataWidth,pFlows,pBlSize,pLutMem,pGlobSt) cmdCoverageWrite = new(port, name);
      // Insert class into list
      cmdListWrite.push_back(cmdCoverageWrite);
    endtask : addGeneralInterfaceWrite

    // -- Add interface Tx for command coverage ----------------------------------
    task addGeneralInterfaceMonitor (virtual iMemRead.tb #(pDataWidth,pFlows,pBlSize) port,
                                     string name);
      // Create commands coverage class
      CommandsCoverageMonitor #(pDataWidth,pFlows,pBlSize) cmdCoverageMonitor = new(port, name);
      // Insert class into list
      cmdListMonitor.push_back(cmdCoverageMonitor);
    endtask : addGeneralInterfaceMonitor

    // -- Enable coverage measures --------------------------------------------
    // Enable coverage measres
    task setEnabled();
      foreach (cmdListWrite[i])   cmdListWrite[i].setEnabled();     // Enable for commands
      foreach (cmdListMonitor[i]) cmdListMonitor[i].setEnabled();   // Enable for commands
    endtask : setEnabled

    // -- Disable coverage measures -------------------------------------------
    // Disable coverage measures
    task setDisabled();
      foreach (cmdListWrite[i])   cmdListWrite[i].setDisabled();     // Disable for commands
      foreach (cmdListMonitor[i]) cmdListMonitor[i].setDisabled();   // Disable for commands
    endtask : setDisabled

    // ------------------------------------------------------------------------
    // Display coverage statistic
    virtual task display();
      $write("----------------------------------------------------------------\n");
      $write("-- COVERAGE STATISTICS:\n");
      $write("----------------------------------------------------------------\n");
      foreach (cmdListWrite[i])   cmdListWrite[i].display();
      foreach (cmdListMonitor[i]) cmdListMonitor[i].display();
      $write("----------------------------------------------------------------\n");
    endtask
  endclass : Coverage
