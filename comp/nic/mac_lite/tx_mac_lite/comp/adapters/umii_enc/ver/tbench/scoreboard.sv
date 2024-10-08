// scoreboard.sv
// Copyright (C) 2019 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

import sv_common_pkg::*;
import sv_mii_pkg::*;
import sv_mfb_pkg::*;
import test_pkg::*;

class ScoreboardDriverCbs extends DriverCbs;
    TransactionTable #(1) sc_table;

    function new (TransactionTable #(1) st);
        sc_table = st;
    endfunction

    virtual task pre_tx(ref Transaction transaction, string inst);
    endtask

    virtual task post_tx(Transaction transaction, string inst);
        MiiTransaction miiTrans;
        MfbTransaction #(ITEM_WIDTH) mfbTrans;

        $cast(mfbTrans, transaction);

        miiTrans = new;
        miiTrans.data = new[mfbTrans.data.size - 4](mfbTrans.data);

        for (int i=0;i<4;i++) begin
            miiTrans.crc[i] = mfbTrans.data[mfbTrans.data.size - 4 + i];
        end

        $cast(transaction, miiTrans);
        sc_table.add(transaction);
    endtask
endclass

class ScoreboardMonitorCbs extends MonitorCbs;
    TransactionTable #(1) sc_table;
    int cnt = 0;

    function new (TransactionTable #(1) st);
        sc_table = st;
    endfunction

    virtual task post_rx(Transaction transaction, string inst);
        bit status=0;
        cnt = cnt + 1;
        //$write("New MII transaction received, time: %t\n", $time);
        sc_table.remove(transaction, status);
        if (status==0)begin
            $write("Unknown transaction received from monitor %s\n", inst);
            $timeformat(-9, 3, " ns", 8);
            $write("Time: %t\n", $time);
            transaction.display();
            sc_table.display();
            $stop;
        end;
        if ((cnt % 5000) == 0) begin
            $write("%0d transactions received.\n", cnt);
        end;
    endtask
endclass

class Scoreboard;
    TransactionTable #(1) scoreTable;
    ScoreboardDriverCbs   driverCbs;
    ScoreboardMonitorCbs  monitorCbs;

    function new ();
        scoreTable = new;
        driverCbs  = new(scoreTable);
        monitorCbs = new(scoreTable);
    endfunction

    task display();
        scoreTable.display();
    endtask
endclass
