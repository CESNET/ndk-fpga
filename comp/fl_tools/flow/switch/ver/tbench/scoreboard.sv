/*
 * scoreboard.sv: Frame Link SWITCH Scoreboard
 * Copyright (C) 2009 CESNET
 * Author(s): Marek Santa <santa@liberouter.org>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 *
 *
 * TODO:
 *
 */

import sv_common_pkg::*;
import sv_fl_pkg::*;

  // --------------------------------------------------------------------------
  // -- Frame Link Driver Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardDriverCbs #(int pFlows = 4,
                              int pIfNumOffset = 0) extends DriverCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable #(1) sc_table[] = new[pFlows];

    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    // Create a class
    function new (TransactionTable #(1) sc_table[]);
      this.sc_table = sc_table;
    endfunction

    // ------------------------------------------------------------------------
    // Function is called before is transaction sended
    // Allow modify transaction before is sended
    virtual task pre_tx(ref Transaction transaction, string inst);
    //   FrameLinkTransaction tr;
    //   $cast(tr,transaction);

    // Example - set first byte of first packet in each frame to zero
    //   tr.data[0][0]=0;
    endtask

    // ------------------------------------------------------------------------
    // Function is called after is transaction sended

    virtual task post_tx(Transaction transaction, string inst);
      FrameLinkTransaction tr;
      bit [pFlows - 1:0] mark = 0;
      string trLabel;
      int byteNo = pIfNumOffset/8;
      int bitNo  = pIfNumOffset%8;

      $cast(tr,transaction);

      $write("byteNo = %0d, bitNo = %0d\n", byteNo, bitNo);
      $write("tr.data = %0h\n", tr.data[0][byteNo]);

      // Get info from correct packet part and offset
      if (pIfNumOffset + pFlows <= tr.data[0].size * 8) begin
        if (bitNo + pFlows > 8) begin
          int i = 0;
          for (int j = bitNo; j < 8; i++, j++)
            mark[i] = tr.data[0][byteNo][j];
          for (int j = 0; i < pFlows; i++, j++)
            mark[i] = tr.data[0][byteNo+1][j];
        end
        else
          for (int i = 0, j = bitNo; i < pFlows; i++, j++)
            mark[i] = tr.data[0][byteNo][j];
      end
      else $write("Header is too short\n");

      // Choose correct transaction table
      for (int i=0; i<pFlows; i++)
        if (mark[i]==1) sc_table[i].add(transaction);

      `ifdef DEBUG

        trLabel = $sformatf("Output interfaces bitmap: %b", mark);
        transaction.display(trLabel);
      `endif
    endtask

   endclass : ScoreboardDriverCbs


  // --------------------------------------------------------------------------
  // -- Frame Link Monitor Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardMonitorCbs #(int pFlows = 4) extends MonitorCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable #(1) sc_table[] = new[pFlows];

    // -- Constructor ---------------------------------------------------------
    // Create a class
    function new (TransactionTable #(1) sc_table[]);
      this.sc_table = sc_table;
    endfunction

    // ------------------------------------------------------------------------
    // Function is called after is transaction received (scoreboard)

    virtual task post_rx(Transaction transaction, string inst);
      bit status=0;
      // Gets number of transaction table from instance name
      int i;
      string tableLabel;

      for(i=0; i< pFlows; i++) begin
        string monitorLabel;
        monitorLabel = $sformatf( "Monitor %0d", i);
        if (monitorLabel == inst) break;
      end

      sc_table[i].remove(transaction, status);
      if (status==0)begin
         tableLabel = $sformatf( "TX%0d", i);
         $write("Unknown transaction received from monitor %d\n", inst);
         transaction.display();
         sc_table[i].display(.inst(tableLabel));
         $stop;
       end
    endtask

  endclass : ScoreboardMonitorCbs

  // -- Constructor ---------------------------------------------------------
  // Create a class
  // --------------------------------------------------------------------------
  // -- Scoreboard
  // --------------------------------------------------------------------------
  class Scoreboard #(int pFlows = 4, int pIfNumOffset = 0);
    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable #(1) scoreTable[];
    ScoreboardMonitorCbs #(pFlows) monitorCbs;
    ScoreboardDriverCbs  #(pFlows, pIfNumOffset) driverCbs;

    // -- Constructor ---------------------------------------------------------
    // Create a class
    function new ();
      this.scoreTable = new[pFlows];
      foreach(this.scoreTable[i])
        this.scoreTable[i] = new();

      this.monitorCbs = new(scoreTable);
      this.driverCbs  = new(scoreTable);
    endfunction

    // -- Display -------------------------------------------------------------
    // Create a class
    task display();
      foreach(this.scoreTable[i])
        scoreTable[i].display();
    endtask

  endclass : Scoreboard

