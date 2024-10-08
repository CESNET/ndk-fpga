/*
 * flu_command_coverage: Frame Link Unaligned Coverage class -
 * transaction coverage
 * Copyright (C) 2011 CESNET
 * Author(s): Viktor Pus <pus@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 * TODO:
 *
 */

/**
 * Frame Link Unaligned Command Coverage for Interface FrameLinkURx.
 * This class measures exercised combinations of interface signals.
 */
class CommandsCoverageURx #(int pDataWidth=512, int pEopWidth=6, int pSopWidth=3);

   //! Interface on witch is covering measured
   virtual iFrameLinkURx#(pDataWidth,pEopWidth,pSopWidth).tb flu;
   //! Instance name
   string  instanceName;

   //! Sampling is enabled
   bit enabled;

   // Sampled values from interface
   logic sop;
   logic eop;
   logic [pEopWidth-1:0] eop_pos;
   logic [pSopWidth-1:0] sop_pos;
   logic src_rdy;
   logic dst_rdy;

   /**
    * Covering transactions.
    */
   covergroup CommandsCovergroup;
      // Start of packet coverpoint
      sop: coverpoint sop {
         bins sop0 = {0};
         bins sop1 = {1};
      }
      // End of packet coverpoint
      eop: coverpoint eop {
         bins eop0 = {0};
         bins eop1 = {1};
      }
      // sop_pos coverpoint
      sop_pos: coverpoint sop_pos;
      // eop_pos coverpoint
      eop_pos: coverpoint eop_pos;

      // Source ready coverpoint
      src_rdy: coverpoint src_rdy {
         bins src_rdy0 = {0};
         bins src_rdy1 = {1};
      }
      // Destination ready coverpoint
      dst_rdy: coverpoint dst_rdy {
         bins dst_rdy0 = {0};
         bins dst_rdy1 = {1};
      }

      // Start/End of packet crosspoint
      cross sop, eop, src_rdy, dst_rdy {
      }

      // EOP crospoint
      cross eop_pos, eop {
         // Ignored values
         ignore_bins eop_ignore_vals0 = binsof(eop.eop0);
      }

      // SOP crospoint
      cross sop_pos, sop {
         // Ignored values
         ignore_bins sop_ignore_vals0 = binsof(sop.sop0);
      }

      option.per_instance=1; // Also per instance statistics
   endgroup

   /**
    * Constructor.
    * @param flu Interface pointer
    * @param instanceName Instance Name
    */
   function new (virtual iFrameLinkURx#(pDataWidth,pEopWidth,pSopWidth).tb flu,
                 string instanceName);
      this.flu = flu;                   // Store interface
      CommandsCovergroup = new;       // Create covergroup
      enabled=0;                      // Disable interface sampling
      this.instanceName = instanceName;
   endfunction

   /**
    * Enable commands coverage measures.
    */
   task setEnabled();
      enabled = 1; // Coverage Enabling
      fork
         run();    // Creating coverage subprocess
      join_none;   // Don't wait for ending
   endtask : setEnabled

   /**
    * Disable command coverage measures.
    */
   task setDisabled();
      enabled = 0; // Disable measures
   endtask : setDisabled

   /**
    * Run command coverage measures.
    */
   task run();
       while (enabled) begin            // Repeat while enabled
         @(flu.cb);             // Wait for clock
         // Sample signals values
         eop_pos  = flu.cb.EOP_POS;
         sop_pos  = flu.cb.SOP_POS;
         sop = flu.cb.SOP;
         eop = flu.cb.EOP;
         src_rdy = flu.cb.SRC_RDY;
         dst_rdy = flu.cb.DST_RDY;
         CommandsCovergroup.sample();
      end
   endtask : run

   /**
    * Display coverage statistic.
    */
   task display();
       $write("Commands coverage for %s: %d percent\n",
               instanceName, CommandsCovergroup.get_inst_coverage());
   endtask : display

endclass: CommandsCoverageURx

/**
 * Frame Link Command Coverage for Interface FrameLinkUTx.
 * This class measures exercised combinations of interface signals.
 */
class CommandsCoverageUTx #(int pDataWidth=512, int pEopWidth=6, int pSopWidth=3);

   //! Interface pointer
   virtual iFrameLinkUTx#(pDataWidth,pEopWidth,pSopWidth).monitor flu;
   //! Instance name
   string  instanceName;

   //! Sampling is enabled
   bit enabled;

   // Sampled values from interface
   logic sop;
   logic eop;
   logic [pEopWidth-1:0] eop_pos;
   logic [pSopWidth-1:0] sop_pos;
   logic src_rdy;
   logic dst_rdy;

   /**
    * Covering transactions.
    */
   covergroup CommandsCovergroup;
      // Start of packet coverpoint
      sop: coverpoint sop {
         bins sop0 = {0};
         bins sop1 = {1};
      }
      // End of packet coverpoint
      eop: coverpoint eop {
         bins eop0 = {0};
         bins eop1 = {1};
      }
      // sop_pos coverpoint
      sop_pos: coverpoint sop_pos;
      // eop_pos coverpoint
      eop_pos: coverpoint eop_pos;

      // Source ready coverpoint
      src_rdy: coverpoint src_rdy {
         bins src_rdy0 = {0};
         bins src_rdy1 = {1};
      }
      // Destination ready coverpoint
      dst_rdy: coverpoint dst_rdy {
         bins dst_rdy0 = {0};
         bins dst_rdy1 = {1};
      }

      // Control signals crosspoint
      cross sop, eop, src_rdy, dst_rdy {
      }

      // eop crospoint
      cross eop_pos, eop {
         // Ignored values
         ignore_bins eop_ignore_vals0 = binsof(eop.eop0);
      }

      // sop crospoint
      cross sop_pos, sop {
         // Ignored values
         ignore_bins sop_ignore_vals0 = binsof(sop.sop0);
      }

      option.per_instance=1; // Also per instance statistics
   endgroup

   /**
    * Constructor.
    * @param flu Interface pointer
    @ *param instanceName Instance name
    */
   function new (virtual iFrameLinkUTx#(pDataWidth,pEopWidth,pSopWidth).monitor flu,
                 string instanceName);
      this.flu = flu;                   // Store interface
      CommandsCovergroup = new;       // Create covergroup
      enabled=0;                      // Disable interface sampling
      this.instanceName = instanceName;
   endfunction

   /**
    * Enable commands coverage measures.
    */
   task setEnabled();
      enabled = 1; // Coverage Enabling
      fork
         run();    // Creating coverage subprocess
      join_none;   // Don't wait for ending
   endtask : setEnabled

   /**
    * Disable command coverage measures.
    */
   task setDisabled();
      enabled = 0; // Disable measures
   endtask : setDisabled

   /**
    * Run command coverage measures.
    */
   task run();
      while (enabled) begin            // Repeat while enabled
         @(flu.monitor_cb);             // Wait for clock
         // Sample signals values
         eop_pos  = flu.monitor_cb.EOP_POS;
         sop_pos  = flu.monitor_cb.SOP_POS;
         sop = flu.monitor_cb.SOP;
         eop = flu.monitor_cb.EOP;
         src_rdy = flu.monitor_cb.SRC_RDY;
         dst_rdy = flu.monitor_cb.DST_RDY;
         CommandsCovergroup.sample();
      end
   endtask : run

   /**
    * Display coverage statistic.
    */
   task display();
      $write("Commands coverage for %s: %d percent\n",
              instanceName, CommandsCovergroup.get_inst_coverage());
   endtask : display

endclass: CommandsCoverageUTx

/**
 * FrameLinkUnaligned Coverage.
 * This class measures coverage of commands
 */
class FluCoverage #(int pRXDataWidth=512, int pRXEopWidth=6, int pRXSopWidth=3,
                    int pTXDataWidth=512, int pTXEopWidth=6, int pTXSopWidth=3);
   //! Commands coverage list
   CommandsCoverageURx #(pRXDataWidth, pRXEopWidth, pRXSopWidth) cmdListRx[$];
   //! Commands coverage list
   CommandsCoverageUTx #(pTXDataWidth, pTXEopWidth, pTXSopWidth) cmdListTx[$];

   /**
    * Add RX interface for command coverage.
    * @param port Interface pointer
    * @param name Interface name
    */
   task addFrameLinkUInterfaceRx(
      virtual iFrameLinkURx#(pRXDataWidth, pRXEopWidth, pRXSopWidth).tb port,
      string name);
      // Create commands coverage class
      CommandsCoverageURx #(pRXDataWidth, pRXEopWidth, pRXSopWidth)
         cmdCoverageURx = new(port, name);
      // Insert class into list
      cmdListRx.push_back(cmdCoverageURx);
   endtask : addFrameLinkUInterfaceRx

   /**
    * Add TX interface for command coverage.
    * @param port Interface pointer
    * @param name Interface name
    */
   task addFrameLinkUInterfaceTx(
      virtual iFrameLinkUTx#(pTXDataWidth,pTXEopWidth,pTXSopWidth).monitor port,
      string name);
      // Create commands coverage class
      CommandsCoverageUTx #(pTXDataWidth, pTXEopWidth, pTXSopWidth)
         cmdCoverageUTx = new(port, name);
      // Insert class into list
      cmdListTx.push_back(cmdCoverageUTx);
   endtask : addFrameLinkUInterfaceTx

   /**
    * Enable coverage measres.
    */
   task setEnabled();
      foreach (cmdListRx[i])   cmdListRx[i].setEnabled(); // Enable for commands
      foreach (cmdListTx[i])   cmdListTx[i].setEnabled(); // Enable for commands
   endtask : setEnabled

   /**
    * Disable coverage measures.
    */
   task setDisabled();
      foreach (cmdListRx[i]) cmdListRx[i].setDisabled(); // Disable for commands
      foreach (cmdListTx[i]) cmdListTx[i].setDisabled(); // Disable for commands
   endtask : setDisabled

   /**
    * Display coverage statistic.
    */
   virtual task display();
      $write("------------------------------------------------------------\n");
      $write("-- COVERAGE STATISTICS:\n");
      $write("------------------------------------------------------------\n");
      foreach (cmdListRx[i]) cmdListRx[i].display();
      foreach (cmdListTx[i]) cmdListTx[i].display();
      $write("------------------------------------------------------------\n");
    endtask
endclass : FluCoverage
