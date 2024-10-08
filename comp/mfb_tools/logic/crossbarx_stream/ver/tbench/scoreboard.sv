// crossbarx_stream.vhd: Crossbarx stream
// Copyright (C) 2020 CESNET z. s. p. o.
// Author(s): Daniel Kriz <xkrizd01@vutbr.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

import sv_common_pkg::*;
import sv_mfb_pkg::*;

class ScoreboardDriverCbs extends DriverCbs;

    TransactionTable #(0) sc_table;

    function new (TransactionTable #(0) st);
        sc_table = st;
    endfunction

    virtual task pre_tx(ref Transaction transaction, string inst);
    endtask

    virtual task post_tx(Transaction transaction, string inst);
        MfbTransaction #(MFB_ITEM_WIDTH,EXT_META_WIDTH) tr;
        MfbTransaction #(MFB_ITEM_WIDTH,MFB_META_WIDTH) tr_extended;
        int size_after_extend;
        logic [MFB_META_WIDTH-1 : 0] meta;
        bit discard;
        $cast(tr, transaction);
        tr.check_meta = 1;
        meta = tr.meta[EXT_META_WIDTH : 1];
        discard = tr.meta[0 : 0];
        if (discard == 1) begin
            if(VERBOSE >= 1) begin
                $write("Transaction dropped!\n");
            end
        end else begin

            if (F_EXTEND_START_EN == 1 && F_EXTEND_END_EN == 1) begin
                size_after_extend = tr.data.size() + F_EXTEND_START_SIZE + F_EXTEND_END_SIZE;
            end
            else if (F_EXTEND_START_EN == 1) begin
                size_after_extend = tr.data.size() + F_EXTEND_START_SIZE;
            end
            else if (F_EXTEND_END_EN == 1) begin
                size_after_extend = tr.data.size() + F_EXTEND_END_SIZE;
            end else begin
                size_after_extend = tr.data.size();
            end

            tr_extended = new();
            tr_extended.data = new[size_after_extend];

            if (F_EXTEND_START_EN == 1) begin
                for (int i = 0; i < size_after_extend; i++) begin
                    if (i<F_EXTEND_START_SIZE) begin
                        tr_extended.data[i] = 0;
                    end else begin
                        tr_extended.data[i] = tr.data[i-F_EXTEND_START_SIZE];
                    end
                end
            end else if (F_EXTEND_END_EN == 1) begin
                for (int i = 0; i < size_after_extend; i++) begin
                    if (i>=tr.data.size()) begin
                        tr_extended.data[i] = 0;
                    end else begin
                        tr_extended.data[i] = tr.data[i];
                    end
                end
            end

            if(F_EXTEND_START_EN == 0 && F_EXTEND_END_EN == 0) begin
                tr_extended.data = tr.data;
                tr_extended.meta = meta;
                sc_table.add(tr_extended);
                if (VERBOSE >= 2) begin
                    $write("Transaction added to ScoreBoard table!\n");
                    $write("Transaction: \n");
                    tr.display();
                end
            end else begin
                tr_extended.meta = meta;
                sc_table.add(tr_extended);
                if (VERBOSE >= 2) begin
                    $write("Transaction added to ScoreBoard table!\n");
                    $write("Transaction: \n");
                    //tr_extended.display();
                end
            end

            if(VERBOSE >= 3) begin
                $write("Generated transaction: \n");
                tr.display();
                $write("Reference transaction: \n");
                tr_extended.display();
            end
        end
    endtask

endclass

class ScoreboardMonitorCbs extends MonitorCbs;

    TransactionTable #(0) sc_table;
    int cnt = 0;

    function new (TransactionTable #(0) st);
        this.sc_table = st;
    endfunction

    virtual task post_rx(Transaction transaction, string inst);
        bit status=0;
        MfbTransaction #(MFB_ITEM_WIDTH,MFB_META_WIDTH) tr_zero_part;

        if (VERBOSE >= 3) begin
            $write("Transaction from component: \n");
            transaction.display();
        end

        $cast(tr_zero_part, transaction);

        for (int i=0; i < F_EXTEND_START_SIZE; i++) begin
            if (F_EXTEND_START_EN == 1) begin
                tr_zero_part.data[i] = 0;
            end
        end

        for (int i=0; i < F_EXTEND_END_SIZE; i++) begin
            if (F_EXTEND_END_EN == 1) begin
                int unsigned index = tr_zero_part.data.size()-i-1;
                tr_zero_part.data[index] = 0;
            end
        end

        if (VERBOSE >= 3) begin
            $write("Transaction from component with zeros: \n");
            tr_zero_part.display();
        end

        if (VERBOSE >= 3) begin
            $write("Transaction from Monitor:\n");
            tr_zero_part.display();
        end

        sc_table.remove(transaction, status);
        if (status==0)begin
            $write("Unknown transaction received from monitor %s\n", inst);
            $timeformat(-9, 3, " ns", 8);
            $write("Time: %t\n", $time);
            transaction.display();
            sc_table.display();
            $stop;
        end;
        if (VERBOSE >= 2) begin
            $write("Transaction received.\n");
            $write("Transaction count: %d\n", this.sc_table.removed);
            transaction.display();
        end

        cnt++;
        if (cnt % (TRANSACTION_COUNT/10) == 0) begin
            $write("%4d transactions have been sent/recieved\n", cnt);
        end

    endtask

endclass

class Scoreboard;

    TransactionTable #(0) scoreTable;
    ScoreboardMonitorCbs  monitorCbs;
    ScoreboardDriverCbs   driverCbs;

    function new ();
        scoreTable = new;
        monitorCbs = new (scoreTable);
        driverCbs  = new (scoreTable);
    endfunction

    task display();
        scoreTable.display();
    endtask

endclass
