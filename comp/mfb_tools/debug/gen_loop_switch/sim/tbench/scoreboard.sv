/*
 * file: scoreboard.sv
 * brief: Verification scoreboard
 * author: Jan Kubalek <kubalek@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 * date: 2020
 */

import sv_common_pkg::*;
import sv_mfb_pkg::*;

class ScoreboardDriverCbs extends DriverCbs;

    TransactionTable #(0) sc_table;
    int VERBOSE_LEVEL = 0;

    function new (TransactionTable #(0) st, int VERBOSE_LEVEL=0);
        sc_table = st;
        this.VERBOSE_LEVEL = VERBOSE_LEVEL;
    endfunction

    virtual task pre_tx(ref Transaction transaction, string inst);
    endtask

    virtual task post_tx(Transaction transaction, string inst);
        sc_table.add(transaction);
        if (VERBOSE_LEVEL>0) begin
            $write("New transaction generated from driver %s\n", inst);
            $timeformat(-9, 3, " ns", 8);
            $write("Time: %t\n", $time);
            transaction.display();
        end
    endtask

endclass

class ScoreboardMonitorCbs extends MonitorCbs;

    TransactionTable #(0) sc_table;
    int VERBOSE_LEVEL = 0;

    function new (TransactionTable #(0) st, int VERBOSE_LEVEL=0);
        this.sc_table = st;
        this.VERBOSE_LEVEL = VERBOSE_LEVEL;
    endfunction

    virtual task post_rx(Transaction transaction, string inst);
        bit status=0;
        sc_table.remove(transaction, status);
        if (status==0)begin
            $write("Unknown transaction received from monitor %s\n", inst);
            $timeformat(-9, 3, " ns", 8);
            $write("Time: %t\n", $time);
            transaction.display();
            sc_table.display();
            $stop;
        end else if (VERBOSE_LEVEL>0) begin
            $write("New transaction received from monitor %s\n", inst);
            $timeformat(-9, 3, " ns", 8);
            $write("Time: %t\n", $time);
            transaction.display();
        end
    endtask

endclass

class Scoreboard;

    TransactionTable #(0) scoreTable;
    ScoreboardMonitorCbs  monitorCbs;
    ScoreboardDriverCbs   driverCbs;

    function new (int VERBOSE_LEVEL=0);
        scoreTable = new;
        monitorCbs = new(scoreTable,VERBOSE_LEVEL);
        driverCbs  = new(scoreTable,VERBOSE_LEVEL);
    endfunction

    task display();
        scoreTable.display();
    endtask

endclass
