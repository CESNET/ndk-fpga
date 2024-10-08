/* \scoreboard.sv
 * \brief Verification scoreboard
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2016
 */
/*
 * Copyright (C) 2016 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

import sv_common_pkg::*;
import sv_flu_pkg::*;



class ScoreboardDriverCbs extends DriverCbs;

    TransactionTable #(TR_TABLE_FIRST_ONLY) sc_table;

    function new (TransactionTable #(TR_TABLE_FIRST_ONLY) st);
        sc_table = st;
    endfunction

    virtual task pre_tx(ref Transaction transaction, string inst);
    endtask

    virtual task post_tx(Transaction transaction, string inst);
        sc_table.add(transaction);
    endtask

endclass



class ScoreboardMonitorCbs extends MonitorCbs;

    TransactionTable #(TR_TABLE_FIRST_ONLY) sc_table;

    function new (TransactionTable #(TR_TABLE_FIRST_ONLY) st);
        this.sc_table = st;
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
        end
    endtask

endclass



class Scoreboard;

    TransactionTable #(TR_TABLE_FIRST_ONLY) scoreTable;
    ScoreboardMonitorCbs monitorCbs;
    ScoreboardDriverCbs driverCbs;

    function new ();
        scoreTable = new;
        monitorCbs = new(scoreTable);
        driverCbs  = new(scoreTable);
    endfunction

    task display();
        scoreTable.display();
    endtask

endclass
