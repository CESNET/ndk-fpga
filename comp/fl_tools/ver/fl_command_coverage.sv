/*
 * fl_command_coverage: Frame Link Coverage class - transaction coverage
 * Copyright (C) 2007 CESNET
 * Author(s): Marcela ©imková <xsimko03@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 * TODO:
 *
 */

  // --------------------------------------------------------------------------
  // -- Frame Link Command Coverage for Interface FrameLinkRx
  // --------------------------------------------------------------------------
  // This class measures exercised combinations of interface signals

  class CommandsCoverageRx #(int pDataWidth=32, int pDremWidth=2);

    // Interface on witch is covering measured
    virtual iFrameLinkRx#(pDataWidth,pDremWidth).tb fl;
    string  instanceName;

    // Sampling is enabled
    bit enabled;

    // Sampled values from interface
    logic sof_n;
    logic eof_n;
    logic sop_n;
    logic eop_n;
    logic [pDremWidth-1:0] drem;
    logic src_rdy_n;
    logic dst_rdy_n;

    //-- Covering transactions ----------------------------------------------
    covergroup CommandsCovergroup;
      // Start of frame coverpoint
      sof: coverpoint sof_n {
        bins sof0 = {0};
        bins sof1 = {1};
        }
      // End of frame coverpoint
      eof: coverpoint eof_n {
        bins eof0 = {0};
        bins eof1 = {1};
        }
      // Start of packet coverpoint
      sop: coverpoint sop_n {
        bins sop0 = {0};
        bins sop1 = {1};
        }
      // End of packet coverpoint
      eop: coverpoint eop_n {
        bins eop0 = {0};
        bins eop1 = {1};
        }
      // Drem coverpoint
      drem: coverpoint drem;

      // Source ready coverpoint
      src_rdy: coverpoint src_rdy_n {
        bins src_rdy0 = {0};
        bins src_rdy1 = {1};
      }
      // Destination ready coverpoint
      dst_rdy: coverpoint dst_rdy_n {
        bins dst_rdy0 = {0};
        bins dst_rdy1 = {1};
      }

      // End of packet crosspoint
      cross sof, sop, eof, eop, src_rdy, dst_rdy {
        // Ilegal values
        illegal_bins ilegal_vals0 = binsof(sop.sop1) && binsof(sof.sof0) && binsof(src_rdy.src_rdy0);
        illegal_bins ilegal_vals1 = binsof(eop.eop1) && binsof(eof.eof0) && binsof(src_rdy.src_rdy0);
        }

      // Drem crospoint
      cross drem, eop {
        // Ilegal values
        ignore_bins drem_ignore_vals0 = binsof(eop.eop1);
        }

        option.per_instance=1; // Also per instance statistics
     endgroup

    // ------------------------------------------------------------------------
    // Constructor

    function new (virtual iFrameLinkRx#(pDataWidth,pDremWidth).tb fl,
                  string instanceName);
      this.fl = fl;                   // Store interface
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
         @(fl.cb);             // Wait for clock
         // Sample signals values
         drem  = fl.cb.DREM;
         sof_n = fl.cb.SOF_N;
         eof_n = fl.cb.EOF_N;
         sop_n = fl.cb.SOP_N;
         eop_n = fl.cb.EOP_N;
         src_rdy_n = fl.cb.SRC_RDY_N;
         dst_rdy_n = fl.cb.DST_RDY_N;
         CommandsCovergroup.sample();
      end
    endtask : run

    // ------------------------------------------------------------------------
    // Display coverage statistic
    task display();
       $write("Commands coverage for %s: %d percent\n",
               instanceName, CommandsCovergroup.get_inst_coverage());
    endtask : display

  endclass: CommandsCoverageRx

  // --------------------------------------------------------------------------
  // -- Frame Link Command Coverage for Interface FrameLinkTx
  // --------------------------------------------------------------------------
  // This class measures exercised combinations of interface signals

  class CommandsCoverageTx #(int pDataWidth=32, int pDremWidth=2);

    // Interface on witch is covering measured
    virtual iFrameLinkTx#(pDataWidth,pDremWidth).monitor fl;
    string  instanceName;

    // Sampling is enabled
    bit enabled;

    // Sampled values from interface
    logic sof_n;
    logic eof_n;
    logic sop_n;
    logic eop_n;
    logic [pDremWidth-1:0] drem;
    logic src_rdy_n;
    logic dst_rdy_n;

    //-- Covering transactions ----------------------------------------------
    covergroup CommandsCovergroup;
      // Start of frame coverpoint
      sof: coverpoint sof_n {
        bins sof0 = {0};
        bins sof1 = {1};
        }
      // End of frame coverpoint
      eof: coverpoint eof_n {
        bins eof0 = {0};
        bins eof1 = {1};
        }
      // Start of packet coverpoint
      sop: coverpoint sop_n {
        bins sop0 = {0};
        bins sop1 = {1};
        }
      // End of packet coverpoint
      eop: coverpoint eop_n {
        bins eop0 = {0};
        bins eop1 = {1};
        }
      // Drem coverpoint
      drem: coverpoint drem;

      // Source ready coverpoint
      src_rdy: coverpoint src_rdy_n {
        bins src_rdy0 = {0};
        bins src_rdy1 = {1};
      }
      // Destination ready coverpoint
      dst_rdy: coverpoint dst_rdy_n {
        bins dst_rdy0 = {0};
        bins dst_rdy1 = {1};
      }

      // Control signals crosspoint
      cross sof, sop, eof, eop, src_rdy, dst_rdy {
        // Ilegal values
        illegal_bins ilegal_vals0 = binsof(sop.sop1) && binsof(sof.sof0) && binsof(src_rdy.src_rdy0);
        illegal_bins ilegal_vals1 = binsof(eop.eop1) && binsof(eof.eof0) && binsof(src_rdy.src_rdy0);
        }

      // Drem crospoint
      cross drem, eop {
        // Ilegal values
        ignore_bins drem_ignore_vals0 = binsof(eop.eop1);
        }

        option.per_instance=1; // Also per instance statistics
     endgroup

    // ------------------------------------------------------------------------
    // Constructor

    function new (virtual iFrameLinkTx#(pDataWidth,pDremWidth).monitor fl,
                  string instanceName);
      this.fl = fl;                   // Store interface
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
         @(fl.monitor_cb);             // Wait for clock
         // Sample signals values
         drem  = fl.monitor_cb.DREM;
         sof_n = fl.monitor_cb.SOF_N;
         eof_n = fl.monitor_cb.EOF_N;
         sop_n = fl.monitor_cb.SOP_N;
         eop_n = fl.monitor_cb.EOP_N;
         src_rdy_n = fl.monitor_cb.SRC_RDY_N;
         dst_rdy_n = fl.monitor_cb.DST_RDY_N;
         CommandsCovergroup.sample();
      end
    endtask : run

    // ------------------------------------------------------------------------
    // Display coverage statistic
    task display();
       $write("Commands coverage for %s: %d percent\n",
               instanceName, CommandsCovergroup.get_inst_coverage());
    endtask : display

  endclass: CommandsCoverageTx

  // --------------------------------------------------------------------------
  // -- Frame Link Coverage
  // --------------------------------------------------------------------------
  // This class measure coverage of commands
  class Coverage #(int pRXDataWidth=32, int pRXDremWidth=2,
                   int pTXDataWidth=32, int pTXDremWidth=2) ;
    CommandsCoverageRx #(pRXDataWidth, pRXDremWidth)   cmdListRx[$];  // Commands coverage list
    CommandsCoverageTx #(pTXDataWidth, pTXDremWidth)   cmdListTx[$];  // Commands coverage list

    // -- Add interface Rx for command coverage ----------------------------------
    task addFrameLinkInterfaceRx ( virtual iFrameLinkRx#(pRXDataWidth, pRXDremWidth).tb port,
                                   string name);
      // Create commands coverage class
      CommandsCoverageRx #(pRXDataWidth, pRXDremWidth) cmdCoverageRx = new(port, name);
      // Insert class into list
      cmdListRx.push_back(cmdCoverageRx);
    endtask : addFrameLinkInterfaceRx

    // -- Add interface Tx for command coverage ----------------------------------
    task addFrameLinkInterfaceTx ( virtual iFrameLinkTx#(pTXDataWidth, pTXDremWidth).monitor port,
                                   string name);
      // Create commands coverage class
      CommandsCoverageTx #(pTXDataWidth, pTXDremWidth) cmdCoverageTx = new(port, name);
      // Insert class into list
      cmdListTx.push_back(cmdCoverageTx);
    endtask : addFrameLinkInterfaceTx

    // -- Enable coverage measures --------------------------------------------
    // Enable coverage measres
    task setEnabled();
      foreach (cmdListRx[i])   cmdListRx[i].setEnabled();   // Enable for commands
      foreach (cmdListTx[i])   cmdListTx[i].setEnabled();   // Enable for commands
    endtask : setEnabled

    // -- Disable coverage measures -------------------------------------------
    // Disable coverage measures
    task setDisabled();
      foreach (cmdListRx[i]) cmdListRx[i].setDisabled();     // Disable for commands
      foreach (cmdListTx[i]) cmdListTx[i].setDisabled();     // Disable for commands
    endtask : setDisabled

    // ------------------------------------------------------------------------
    // Display coverage statistic
    virtual task display();
      $write("----------------------------------------------------------------\n");
      $write("-- COVERAGE STATISTICS:\n");
      $write("----------------------------------------------------------------\n");
      foreach (cmdListRx[i]) cmdListRx[i].display();
      foreach (cmdListTx[i]) cmdListTx[i].display();
      $write("----------------------------------------------------------------\n");
    endtask
  endclass : Coverage


