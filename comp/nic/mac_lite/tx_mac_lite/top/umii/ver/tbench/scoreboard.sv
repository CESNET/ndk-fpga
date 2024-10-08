// scoreboard.sv
// Copyright (C) 2020 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

import sv_common_pkg::*;
import sv_mfb_pkg::*;
import sv_mii_pkg::*;
import crc32_ethernet_pkg::*;

class ScoreboardDriverCbs extends DriverCbs;
    TransactionTable #(1) sc_table;
    longint discardedFrames;
    longint sentFrames;
    longint lencnt;

    function new (TransactionTable #(1) st);
        sc_table = st;
        this.discardedFrames = 0;
        this.sentFrames = 0;
        this.lencnt = 0;
    endfunction

    virtual task pre_tx(ref Transaction transaction, string inst);
    endtask

    virtual task post_tx(Transaction transaction, string inst);
        int len_fix;
        int len_with_crc;
        MiiTransaction miiTrans;
        MfbTransaction #(RX_ITEM_WIDTH) mfbTrans;
        bit [32-1 : 0] crc_value;
        byte crc[3 : 0];

        $cast(mfbTrans, transaction);

        len_fix = RX_INCLUDE_CRC ? 0 : 4;
        len_with_crc = mfbTrans.data.size() + len_fix;

        if (RX_INCLUDE_CRC == 0) begin
            crc_value = ~crc32_ethernet(mfbTrans.data, 32'hffffffff);
            crc = {<< byte{crc_value}};
            //$write("CRC value %h\n", crc_value);
            mfbTrans.data = new[len_with_crc](mfbTrans.data);
            // Insert CRC to data
            for (int i = 0; i<4; i++) begin
                mfbTrans.data[len_with_crc-1-i] = crc[i];
            end
        end

        // conversion to MII
        miiTrans = new;
        miiTrans.data = new[mfbTrans.data.size - 4](mfbTrans.data);

        for (int i=0;i<4;i++) begin
            miiTrans.crc[i] = mfbTrans.data[mfbTrans.data.size - 4 + i];
        end

        $cast(transaction, miiTrans);

        if (len_with_crc >= 64) begin
            this.sentFrames++;
            this.lencnt = this.lencnt + len_with_crc;
            sc_table.add(transaction);
        end else begin
            this.discardedFrames++;
        end
    endtask

endclass

class ScoreboardMonitorCbs extends MonitorCbs;
    TransactionTable #(1) sc_table;
    int cnt = 0;

    function new (TransactionTable #(1) st);
        this.sc_table = st;
    endfunction

    virtual task post_rx(Transaction transaction, string inst);
        bit status=0;
        cnt = cnt + 1;
        sc_table.remove(transaction, status);
        if (status==0)begin
            $write("Unknown transaction received from monitor %s\n", inst);
            $timeformat(-9, 3, " ns", 8);
            $write("Time: %t\n", $time);
            transaction.display();
            sc_table.display();
            $stop;
        end;
        if ((cnt % 1000) == 0) begin
            $write("%0d transactions received.\n", cnt);
        end;
    endtask
endclass

class Scoreboard;
    string inst;

    TransactionTable #(1) scoreTable;
    ScoreboardMonitorCbs  monitorCbs;
    ScoreboardDriverCbs   driverCbs;

    function new ();
        inst = inst;
        scoreTable = new;
        monitorCbs = new(scoreTable);
        driverCbs  = new(scoreTable);
    endfunction

    task display();
        scoreTable.display(.inst(inst));
        $write("Total Processed Bytes by Model:\t\t %10d\n", this.driverCbs.lencnt);
    endtask

    function longint getByteCounter();
        return this.driverCbs.lencnt;
    endfunction;

    function longint getDiscardedFramesCounter();
        return this.driverCbs.discardedFrames;
    endfunction;

    function longint getSentFramesCounter();
        return this.driverCbs.sentFrames;
    endfunction;
endclass
