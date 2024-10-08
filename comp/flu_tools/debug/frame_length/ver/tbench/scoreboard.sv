/*!
 * \file scoreboard.sv
 * \brief Main Scoreboard
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2018
 */
/*
 * Copyright (C) 2018 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

import sv_common_pkg::*;
import sv_flu_pkg::*;
import sv_wl_pkg::*;


  class ScoreboardDriverCbs extends DriverCbs;
    TransactionTable sc_table;

    // -- Constructor ---------------------------------------------------------
    // Create a class
    function new (TransactionTable sc_table);
      this.sc_table = sc_table;
    endfunction

    // ------------------------------------------------------------------------
    // Function is called after is transaction sended
    virtual task post_tx(Transaction transaction, string inst);
       FrameLinkUTransaction flut;
       WordLinkTransaction wlt;
       assert($cast(flut,transaction));
       wlt = new;
       wlt.data = new[2];
       wlt.data[0] = flut.data.size & 'hff;
       wlt.data[1] = flut.data.size >> 8;
       sc_table.add(wlt);
    endtask
  endclass : ScoreboardDriverCbs



  class ScoreboardMonitorCbs extends MonitorCbs;
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



  class Scoreboard;
    TransactionTable     scoreTable;
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
