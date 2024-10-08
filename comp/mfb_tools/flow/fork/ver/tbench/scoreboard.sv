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
import sv_mfb_pkg::*;

class ScoreboardDriverCbs extends DriverCbs;

    TransactionTable #(0) sc_table[OUTPUT_PORTS];

    function new (TransactionTable #(0) st[OUTPUT_PORTS]);
        sc_table = st;
    endfunction

    virtual task pre_tx(ref Transaction transaction, string inst);
    endtask

    virtual task post_tx(Transaction transaction, string inst);
        MfbTransaction #(ITEM_WIDTH,META_WIDTH) tr;
        $cast(tr, transaction);
        tr.check_meta = 1;
        if(VERBOSE >=1)begin
            tr.display();
        end
        tr.copy();
        foreach(sc_table[i]) begin
            sc_table[i].add(tr);
        end
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

    TransactionTable #(0) scoreTable[OUTPUT_PORTS];
    ScoreboardMonitorCbs  monitorCbs[OUTPUT_PORTS];
    ScoreboardDriverCbs   driverCbs;

    function new ();
        foreach(scoreTable[i]) begin
            scoreTable[i] = new;
        end
        foreach(monitorCbs[i]) begin
            monitorCbs[i] = new(scoreTable[i]);
        end
        driverCbs  = new(scoreTable);
    endfunction

    task display();
        foreach(scoreTable[i]) begin
            scoreTable[i].display();
        end
    endtask

endclass
