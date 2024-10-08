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
import sv_fl_pkg::*;
import sv_flu_pkg::*;

  // --------------------------------------------------------------------------
  // -- Frame Link Driver Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardDriverCbs extends DriverCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable #(TR_TABLE_FIRST_ONLY) sc_table;

    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    // Create a class
    function new (TransactionTable #(TR_TABLE_FIRST_ONLY) sc_table);
      this.sc_table = sc_table;
    endfunction

    // ------------------------------------------------------------------------
    // Function is called after is transaction sended

    virtual task post_tx(Transaction transaction, string inst);
       // transaction.display("DRIVER");
       sc_table.add(transaction);
    endtask

   endclass : ScoreboardDriverCbs


  // --------------------------------------------------------------------------
  // -- Frame Link Monitor Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardMonitorCbs extends MonitorCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable #(TR_TABLE_FIRST_ONLY) sc_table;

    // -- Constructor ---------------------------------------------------------
    // Create a class
    function new (TransactionTable #(TR_TABLE_FIRST_ONLY) sc_table);
      this.sc_table = sc_table;
    endfunction

    // ------------------------------------------------------------------------
    // Function is called after is transaction received (scoreboard)

    virtual task post_rx(Transaction transaction, string inst);
      bit status=0;
      FrameLinkUTransaction tr;
      FrameLinkTransaction to;

      //transaction.display("MONITOR");
      $cast(to, transaction);

      tr = new();

      tr.data          = new[to.data[0].size];
      tr.data          = to.data[0];
      tr.packetSizeMax = to.packetSizeMax[0];
      tr.packetSizeMin = to.packetSizeMin[0];

      //tr.display("Monitor0");
      sc_table.remove(tr, status);
      if (status==0)begin
         $write("Unknown transaction received from monitor %d\n", inst);
         tr.display();
         sc_table.display();
         $stop;
       end;
    endtask


  endclass : ScoreboardMonitorCbs

  // -- Constructor ---------------------------------------------------------
  // Create a class
  // --------------------------------------------------------------------------
  // -- Scoreboard
  // --------------------------------------------------------------------------
  class Scoreboard;
    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable     #(TR_TABLE_FIRST_ONLY) scoreTable;
    ScoreboardMonitorCbs monitorCbs;
    ScoreboardDriverCbs  driverCbs;

    // -- Constructor ---------------------------------------------------------
    // Create a class
    function new ();
      this.scoreTable = new;
      this.monitorCbs = new(scoreTable);
      this.driverCbs  = new(scoreTable);
    endfunction

    // -- Display -------------------------------------------------------------
    // Create a class
    task display();
      scoreTable.display();
    endtask

  endclass : Scoreboard

