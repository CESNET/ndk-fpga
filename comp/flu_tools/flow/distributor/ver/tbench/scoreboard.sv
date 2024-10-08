/*
 * scoreboard.sv: Frame Link Scoreboard
 * Copyright (C) 2012 CESNET
 * Author(s): Lukas Kekely <kekely@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 *
 *
 * TODO:
 *
 */

import sv_common_pkg::*;
import sv_flu_pkg::*;
import math_pkg::*;

  // --------------------------------------------------------------------------
  // -- Frame Link Driver Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardDriverCbs #(int pFlows = 4) extends DriverCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable #(TR_TABLE_FIRST_ONLY) sc_table[] = new[pFlows];
    bit inum_mask[$][pFlows];
    Transaction t[$];
    int t_flag, i_flag;


    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    // Create a class
    function new (TransactionTable #(TR_TABLE_FIRST_ONLY) sc_table[]);
      this.sc_table = sc_table;
    endfunction

    virtual task pre_tx(ref Transaction transaction, string inst);
      Transaction tr;
      FrameLinkUTransaction tr_flu;
      bit x[pFlows];

      if("Driver0" == inst) begin
        t.push_back(transaction);
      end;

      if("DriverI" == inst) begin
        $cast(tr_flu,transaction);
        for(int i=0; i<pFlows; i++)
          x[i]=tr_flu.data[i/8][i%8];
        inum_mask.push_back(x);
        //transaction.display(inst);
      end;

      if(t.size() && inum_mask.size()) begin
        x=inum_mask.pop_front();
        tr=t.pop_front();
        $cast(tr_flu,tr);
        $write(inum_mask);
        for(int i=0; i<pFlows; i++)
          if(x[i])
            sc_table[i].add(tr_flu);
      end;

      //transaction.display(inst);
    endtask

    // ------------------------------------------------------------------------
    // Function is called after is transaction sended

    virtual task post_tx(Transaction transaction, string inst);
    endtask

   endclass : ScoreboardDriverCbs


  // --------------------------------------------------------------------------
  // -- Frame Link Monitor Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardMonitorCbs #(int pFlows = 4) extends MonitorCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable #(TR_TABLE_FIRST_ONLY) sc_table[] = new[pFlows];

    // -- Constructor ---------------------------------------------------------
    // Create a class
    function new (TransactionTable #(TR_TABLE_FIRST_ONLY) sc_table[]);
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

      //transaction.display(inst);
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
  class Scoreboard #(int pFlows = 4);

    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable #(TR_TABLE_FIRST_ONLY) scoreTable[];
    ScoreboardMonitorCbs #(pFlows) monitorCbs;
    ScoreboardDriverCbs  #(pFlows) driverCbs;

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
      string tableLabel;

      foreach(this.scoreTable[i]) begin
        tableLabel = $sformatf( "TX%0d", i);
        scoreTable[i].display(.inst(tableLabel));
      end
    endtask

  endclass : Scoreboard
