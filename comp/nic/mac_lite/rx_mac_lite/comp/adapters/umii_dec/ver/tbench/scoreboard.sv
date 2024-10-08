// scoreboard.sv
// Copyright (C) 2019 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

import sv_common_pkg::*;
import sv_mii_pkg::*;
import sv_mfb_pkg::*;
import test_pkg::*;

class ScoreboardMiiDriverCbs extends DriverCbs;
    TransactionTable #(1) sc_table;
    int i;

    function new (int index, TransactionTable #(1) st);
        sc_table = st;
        i = index;
    endfunction

    virtual task pre_tx(ref Transaction transaction, string inst);
    endtask

    virtual task post_tx(Transaction transaction, string inst);
        MiiTransaction               mii_tr;
        MfbTransaction #(ITEM_WIDTH) mfb_tr;
        int mii_tr_size;

        //$write("New GMII transaction send to DUT, time: %t\n", $time);
        $cast(mii_tr, transaction);
        //mii_tr.display();
        mii_tr_size = mii_tr.data.size;

        // create MFB transaction and copy data
        mfb_tr = new();
        mfb_tr.data = new[mii_tr_size+4](mii_tr.data);

        // add CRC to MFB transaction
        for (int i=0; i<4; i++) begin
            mfb_tr.data[mii_tr_size+i] = mii_tr.crc[i];
        end

        //mfb_tr.display();
        if (TRANSACTION_CHECK[i]) begin
            sc_table.add(mfb_tr);
        end
    endtask
endclass

class ScoreboardMfbMonitorCbs extends MonitorCbs;
    TransactionTable #(1) sc_table;
    int cnt = 0;
    int i;

    function new (int index, TransactionTable #(1) st);
        sc_table = st;
        i = index;
    endfunction

    virtual task post_rx(Transaction transaction, string inst);
        bit status=0;
        //$write("New MFB transaction received, time: %t\n", $time);
        cnt = cnt + 1;
        if (TRANSACTION_CHECK[i]) begin
            sc_table.remove(transaction, status);
        end else begin
            status=1;
        end
        if (status==0)begin
            $write("Unknown transaction received from monitor %s\n", inst);
            $timeformat(-9, 3, " ns", 8);
            $write("Time: %t\n", $time);
            transaction.display();
            sc_table.display();
            $stop;
        end;
        if ((cnt % 10000) == 0) begin
            $write("%0d transactions received.\n", cnt);
        end;
    endtask
endclass

class Scoreboard;
    TransactionTable #(1)   scoreTable;
    ScoreboardMiiDriverCbs  miiDriverCbs;
    ScoreboardMfbMonitorCbs mfbMonitorCbs;

    function new (int index);
        scoreTable    = new;
        miiDriverCbs  = new(index,scoreTable);
        mfbMonitorCbs = new(index,scoreTable);
    endfunction

    task display();
        scoreTable.display();
    endtask
endclass
