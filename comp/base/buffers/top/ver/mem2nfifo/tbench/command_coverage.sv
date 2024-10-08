/*
 * command_coverage: Mem2nFifo Coverage class - transaction coverage
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

  import math_pkg::*;       // log2()

  // --------------------------------------------------------------------------
  // -- Fifo Command Coverage for Interface iGeneral.fifo_write_cb
  // --------------------------------------------------------------------------
  // This class measures exercised combinations of interface signals

  class CommandsCoverageWrite #(int pDataWidth=64,int pFlows=8,int pBlSize=512,int pLutMem=0, pGlobSt=0);

    // Interface on witch is covering measured
    virtual iNFifoTx.mem_write_tb #(pDataWidth,pFlows,pBlSize,pLutMem,pGlobSt) m_w;
    string  instanceName;

    // Sampling is enabled
    bit enabled;

    // Sampled values from interface
    logic [math_pkg::abs($clog2(pFlows)-1):0] block_addr;
    logic [$clog2(20)-1:0] wr_addr;
    logic [$clog2(20)-1:0] new_len;
    logic [pFlows-1:0] new_len_dv;
    logic write;
    logic [pFlows-1:0] full;

    //-- Covering transactions ----------------------------------------------
    covergroup CommandsCovergroup;
      // block_addr coverpoint
      block_addr: coverpoint block_addr;

      // wr_addr coverpoint
      wr_addr: coverpoint wr_addr;

      // new_len coverpoint
      new_len: coverpoint new_len;

      // wr_addr coverpoint
      new_len_dv: coverpoint new_len_dv{
        bins new_len_dv0 = {8'b00000001};
        bins new_len_dv1 = {8'b00000010};
        bins new_len_dv2 = {8'b00000100};
        bins new_len_dv3 = {8'b00001000};
        bins new_len_dv4 = {8'b00010000};
        bins new_len_dv5 = {8'b00100000};
        bins new_len_dv6 = {8'b01000000};
        bins new_len_dv7 = {8'b10000000};
      }

      // write coverpoint
      write: coverpoint write {
        bins write0 = {0};
        bins write1 = {1};
      }

      option.per_instance=1; // Also per instance statistics
     endgroup

    // ------------------------------------------------------------------------
    // Constructor

    function new (virtual iNFifoTx.mem_write_tb #(pDataWidth,pFlows,pBlSize,pLutMem,pGlobSt) m_w,
                  string instanceName);
      this.m_w = m_w;                 // Store interface
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
         @(m_w.mem_write_cb);           // Wait for clock
         // Sample signals values
         block_addr = m_w.mem_write_cb.BLOCK_ADDR;
         wr_addr    = m_w.mem_write_cb.WR_ADDR;
         new_len    = m_w.mem_write_cb.NEW_LEN;
         new_len_dv = m_w.mem_write_cb.NEW_LEN_DV;
         write      = m_w.mem_write_cb.WRITE;
         full       = m_w.mem_write_cb.FULL;

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
  // -- Memory Command Coverage for Interface iGeneral.fifo_monitor_cb
  // --------------------------------------------------------------------------
  // This class measures exercised combinations of interface signals

  class CommandsCoverageMonitor #(int pDataWidth=64,int pFlows=8,int pBlSize=512,int pLutMem=0, pGlobSt=0);

    // Interface on witch is covering measured
    virtual iNFifoTx.nfifo_monitor #(pDataWidth,pFlows,pBlSize,pLutMem,pGlobSt) f_m;
    string  instanceName;

    // Sampling is enabled
    bit enabled;

    // Sampled values from interface
    logic data_vld;
    logic read;
    logic empty;

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

      // empty coverpoint
      empty: coverpoint empty{
        bins empty0 = {0};
        bins empty1 = {1};
      }

      option.per_instance=1; // Also per instance statistics
     endgroup

    // ------------------------------------------------------------------------
    // Constructor

    function new (virtual iNFifoTx.nfifo_monitor #(pDataWidth,pFlows,pBlSize,pLutMem,pGlobSt) f_m,
                  string instanceName);
      this.f_m = f_m;                 // Store interface
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
         @(f_m.nfifo_monitor_cb);        // Wait for clock
         // Sample signals values
         data_vld = f_m.nfifo_monitor_cb.DATA_VLD;
         read     = f_m.nfifo_monitor_cb.READ;
         empty    = f_m.nfifo_monitor_cb.EMPTY;

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
  // -- Mem2nFifo Coverage
  // --------------------------------------------------------------------------
  // This class measure coverage of commands
  class Coverage #(int pDataWidth=64,int pFlows=8,int pBlSize=512,int pLutMem=0, pGlobSt=0);
    // Commands coverage lists
    CommandsCoverageWrite   #(pDataWidth,pFlows,pBlSize,pLutMem,pGlobSt) cmdListWrite[$];
    CommandsCoverageMonitor #(pDataWidth,pFlows,pBlSize,pLutMem,pGlobSt) cmdListMonitor[$];

    // -- Add interface Write for command coverage ----------------------------------
    task addGeneralInterfaceWrite (virtual iNFifoTx.mem_write_tb #(pDataWidth,pFlows,pBlSize,pLutMem,pGlobSt) port,
                                   string name);
      // Create commands coverage class
      CommandsCoverageWrite #(pDataWidth,pFlows,pBlSize,pLutMem,pGlobSt) cmdCoverageWrite = new(port, name);
      // Insert class into list
      cmdListWrite.push_back(cmdCoverageWrite);
    endtask : addGeneralInterfaceWrite

    // -- Add interface Tx for command coverage ----------------------------------
    task addGeneralInterfaceMonitor (virtual iNFifoTx.nfifo_monitor #(pDataWidth,pFlows,pBlSize,pLutMem,pGlobSt) port,
                                     string name);
      // Create commands coverage class
      CommandsCoverageMonitor #(pDataWidth,pFlows,pBlSize,pLutMem,pGlobSt) cmdCoverageMonitor = new(port, name);
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


