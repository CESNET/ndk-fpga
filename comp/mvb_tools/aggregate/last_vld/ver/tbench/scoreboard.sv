/* \scoreboard.sv
 * \brief Verification scoreboard
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2016
 */
/*
 * Copyright (C) 2016 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

import sv_common_pkg::*;
import sv_mvb_pkg::*;



class ScoreboardDriverCbs extends DriverCbs;

    TransactionTable #(TR_TABLE_FIRST_ONLY) sc_table;
    MvbTransaction #(ITEM_WIDTH) last;

    function new (TransactionTable #(TR_TABLE_FIRST_ONLY) st);
        sc_table = st;
        last = null;
    endfunction

    virtual task pre_tx(ref Transaction transaction, string inst);
    endtask

    virtual task post_tx(Transaction transaction, string inst);
        MvbTransaction #(ITEM_WIDTH) tr;
        int n;
        if(last) begin
            $cast(tr, transaction);
            n = tr.stream + (tr.word-last.word)*ITEMS;
            for(int i=last.stream; i < n; i++)
                sc_table.add(last.copy());
        end
        $cast(last, transaction);
    endtask

endclass



class ScoreboardMonitorCbs extends MonitorCbs;

    TransactionTable #(TR_TABLE_FIRST_ONLY) sc_table;
    Transaction q[$];

    function new (TransactionTable #(TR_TABLE_FIRST_ONLY) st);
        this.sc_table = st;
        q = {};
    endfunction

    virtual task post_rx(Transaction transaction, string inst);
        Transaction tr;
        bit status=0;
        q.push_back(transaction);
        while(sc_table.tr_table.size && q.size) begin
            tr = q.pop_front();
            sc_table.remove(tr, status);
            if (status==0)begin
                $write("Unknown transaction received from monitor %s\n", inst);
                $timeformat(-9, 3, " ns", 8);
                $write("Time: %t\n", $time);
                transaction.display();
                sc_table.display();
                $stop;
            end
        end
    endtask

endclass



class Scoreboard;

    TransactionTable #(TR_TABLE_FIRST_ONLY) scoreTable;
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

