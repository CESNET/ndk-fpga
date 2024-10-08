// scoreboard.sv: Verification scoreboard
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kondys <xkondy00@vutbr.cz>
//
// SPDX-License-Identifier: BSD-3-Clause


import sv_common_pkg::*;
import sv_mfb_pkg::*;

class ScoreboardDriverCbs extends DriverCbs;

    TransactionTable #(0) sc_table;

    function new (TransactionTable #(0) st);
        sc_table = st;
    endfunction

    virtual task pre_tx(ref Transaction transaction, string inst);
        MfbTransaction #(test_pkg::ITEM_WIDTH, test_pkg::META_WIDTH) tr;

        $cast(tr, transaction);
        if (tr.data.size() < 60) begin
            //$write("Transaction is undersized, length: %4d\n", tr.data.size());
            tr.meta[0] = 1'b1; // set undersized to '1'
        end else begin
            //$write("Transaction sent, length: %4d\n", tr.data.size());
            tr.meta[0] = 1'b0; // set undersized to '0'
            sc_table.add(tr);
        end;
    endtask

    virtual task post_tx(Transaction transaction, string inst);
    endtask

endclass

class ScoreboardMonitorCbs extends MonitorCbs;

    TransactionTable #(0) sc_table;

    function new (TransactionTable #(0) st);
        this.sc_table = st;
    endfunction

    virtual task post_rx(Transaction transaction, string inst);
        bit status=0;
        MfbTransaction #(test_pkg::ITEM_WIDTH, test_pkg::META_WIDTH) tr;
        $cast(tr, transaction);

        sc_table.remove(transaction, status);
        if ((status==0) && (tr.data.size() >= 60)) begin
            $write("Unknown transaction received from monitor %s\n", inst);
            $timeformat(-9, 3, " ns", 8);
            $write("Time: %t\n", $time);
            transaction.display();
            sc_table.display();
            $stop;
        end;
    endtask

endclass

class Scoreboard;

    TransactionTable #(0) scoreTable;
    ScoreboardMonitorCbs  monitorCbs;
    ScoreboardDriverCbs   driverCbs;

    function new ();
      scoreTable = new;
      monitorCbs = new(scoreTable);
      driverCbs  = new(scoreTable);
    endfunction

    task display();
      scoreTable.display();
    endtask

endclass
