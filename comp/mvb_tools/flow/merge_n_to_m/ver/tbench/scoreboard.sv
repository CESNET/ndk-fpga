/* \scoreboard.sv
 * \brief Verification scoreboard
 * \author Daniel Kříž <xkrizd01@vutbr.cz>
 * \date 2020
 */
 /*
 * Copyright (C) 2020 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

import sv_common_pkg::*;
import sv_mvb_pkg::*;

class ScoreboardDriverCbs extends DriverCbs;

    TransactionTable #(0) sc_table;

    function new (TransactionTable #(0) st);
        sc_table = st;
    endfunction

    virtual task pre_tx(ref Transaction transaction, string inst);
    endtask

    virtual task post_tx(Transaction transaction, string inst);
        MvbTransaction #(DATA_WIDTH) tr;
        $cast(tr, transaction);
        if(VERBOSE >=1)begin
            tr.display();
        end
        sc_table.add(tr);
    endtask

endclass



class ScoreboardMonitorCbs extends MonitorCbs;

    TransactionTable #(0) sc_table;

    function new (TransactionTable #(0) st);
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
