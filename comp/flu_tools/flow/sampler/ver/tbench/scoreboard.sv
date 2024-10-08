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

  // --------------------------------------------------------------------------
  // -- Frame Link Driver Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardDriverCbs extends DriverCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable sc_table;
    integer counter;
    integer DUT_RATE;

    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    // Create a class
    function new (TransactionTable sc_table, integer d);
      this.sc_table = sc_table;
      this.counter=0;
      this.DUT_RATE=d;
    endfunction

    // ------------------------------------------------------------------------
    // Function is called after is transaction sended

    virtual task post_tx(Transaction transaction, string inst);
       // transaction.display("DRIVER");
       if(!counter) sc_table.add(transaction);
       counter++;
       if(counter>DUT_RATE) counter=0;
    endtask

   endclass : ScoreboardDriverCbs


  // --------------------------------------------------------------------------
  // -- Frame Link Monitor Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardMonitorCbs extends MonitorCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable sc_table;

    // -- Constructor ---------------------------------------------------------
    // Create a class
    function new (TransactionTable sc_table);
      this.sc_table = sc_table;
    endfunction

    // ------------------------------------------------------------------------
    // Function is called after is transaction received (scoreboard)

    virtual task post_rx(Transaction transaction, string inst);
      bit status=0;
      sc_table.remove(transaction, status);
      if (status==0)begin
         $write("Unknown transaction received from monitor %d\n", inst);
         transaction.display();
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
    function new (integer DUT_RATE);
      this.scoreTable = new;
      this.monitorCbs = new(scoreTable);
      this.driverCbs  = new(scoreTable,DUT_RATE);
    endfunction

    // -- Display -------------------------------------------------------------
    // Create a class
    task display();
      scoreTable.display(0);
    endtask

  endclass : Scoreboard

