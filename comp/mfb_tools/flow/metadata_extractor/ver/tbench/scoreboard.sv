/* \scoreboard.sv
 * \brief Verification scoreboard
 * \author Daniel Kriz <xkrizd01@vutbr.cz>
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
import sv_mvb_pkg::*;

class ScoreboardDriverCbs extends DriverCbs;

    TransactionTable #(0) sc_table;
    TransactionTable #(0) sc_mvb_table;

    function new (TransactionTable #(0) st, TransactionTable #(0) mvb_st);
        sc_table = st;
        sc_mvb_table = mvb_st;
    endfunction

    virtual task pre_tx(ref Transaction transaction, string inst);
        MfbTransaction #(MFB_ITEM_WIDTH,MFB_META_WIDTH) tr;
        MvbTransaction #(MFB_META_WIDTH) mvb_tr = new();
        $cast(tr, transaction);

        mvb_tr.data = tr.meta;

        if(VERBOSE>=1)begin
            $write("Transaction send \n");
            tr.display();
            mvb_tr.display();
        end;

        sc_table.add(tr);
        sc_mvb_table.add(mvb_tr);
    endtask

    virtual task post_tx(Transaction transaction, string inst);
    endtask

endclass

class ScoreboardMonitorMfbCbs extends MonitorCbs;

    TransactionTable #(0) sc_table;

    function new (TransactionTable #(0) st);
        this.sc_table = st;
    endfunction

    virtual task post_rx(Transaction transaction, string inst);
        bit status=0;
        MfbTransaction #(MFB_ITEM_WIDTH,MFB_META_WIDTH) tr;
        $cast(tr, transaction);
        tr.check_meta = 1;
        sc_table.remove(tr, status);
        if (status==0)begin
            $write("Unknown transaction received from monitor %s\n", inst);
            $timeformat(-9, 3, " ns", 8);
            $write("Time: %t\n", $time);
            tr.display();
            sc_table.display();
            $stop;
        end;
    endtask

endclass

class ScoreboardMonitorMvbCbs extends MonitorCbs;

    TransactionTable #(0) sc_mvb_table;

    function new (TransactionTable #(0) mvb_st);
        this.sc_mvb_table = mvb_st;
    endfunction

    virtual task post_rx(Transaction transaction, string inst);
        MvbTransaction #(MFB_META_WIDTH) mvb_tr;

        bit status=0;
        sc_mvb_table.remove(transaction, status);
        if (status==0)begin
            $write("Unknown transaction received from monitor %s\n", inst);
            $timeformat(-9, 3, " ns", 8);
            $write("Time: %t\n", $time);
            transaction.display();
            sc_mvb_table.display();
            $stop;
        end;
    endtask

endclass

class Scoreboard;

    TransactionTable #(0) scoreTable;
    ScoreboardMonitorMfbCbs monitorCbs;
    ScoreboardDriverCbs driverCbs;

    TransactionTable #(0) mvb_scoreTable;
    ScoreboardMonitorMvbCbs mvb_monitorCbs;

    task setDisabled();
        wait(scoreTable.added == scoreTable.removed);
        wait(mvb_scoreTable.added == mvb_scoreTable.removed);
    endtask

    function new ();
        scoreTable = new;
        mvb_scoreTable = new;
        monitorCbs = new(scoreTable);
        driverCbs  = new(scoreTable, mvb_scoreTable);

        mvb_monitorCbs = new(mvb_scoreTable);
    endfunction

    task display();
        scoreTable.display();
        mvb_scoreTable.display();
    endtask

endclass
