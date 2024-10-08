/* \scoreboard.sv
 * \brief Verification scoreboard
 * \author Jakub Cabal <cabal@cesnet.cz>
 * \date 2017
 */
/*
 * Copyright (C) 2017 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

import sv_common_pkg::*;
import sv_mfb_pkg::*;
import sv_mvb_pkg::*;


class ScoreboardDriverCbs #(int ITEM_WIDTH, int LNG_WIDTH, bit SATURATION) extends DriverCbs;
    TransactionTable #(TR_TABLE_FIRST_ONLY) sc_table;

    function new (TransactionTable #(TR_TABLE_FIRST_ONLY) st);
        sc_table = st;
    endfunction

    virtual task pre_tx(ref Transaction transaction, string inst);
    endtask

    virtual task post_tx(Transaction transaction, string inst);
        MfbTransaction #(ITEM_WIDTH) tr;
        MvbTransaction #(LNG_WIDTH)  lng_tr = new();
        $cast(tr, transaction);

        //$write("tr: \n");
        //tr.display();
        //$write("lng_tr: \n");
        //lng_tr.display();

        lng_tr.data = tr.data.size;
        if (SATURATION) begin
            if (tr.data.size >= 2**LNG_WIDTH) begin
                lng_tr.data = '1;
            end;
        end;

        sc_table.add(lng_tr);
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
        end;
    endtask

endclass


class Scoreboard #(int ITEM_WIDTH, int LNG_WIDTH, bit SATURATION);
    TransactionTable     #(TR_TABLE_FIRST_ONLY)  scoreTable;
    ScoreboardMonitorCbs                         monitorCbs;
    ScoreboardDriverCbs  #(ITEM_WIDTH,LNG_WIDTH,SATURATION) driverCbs;

    function new ();
      scoreTable = new;
      monitorCbs = new(scoreTable);
      driverCbs  = new(scoreTable);
    endfunction

    task display();
      scoreTable.display();
    endtask

endclass
