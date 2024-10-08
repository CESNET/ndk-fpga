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
import sv_mi32_pkg::*;
import math_pkg::*;

class ScoreboardDriverCbs extends DriverCbs;

    TransactionTable #(0) sc_table;
    byte unsigned register[SRC_CHANNELS][4];
    int ch_cnt[SRC_CHANNELS];

    function new (TransactionTable #(0) st, byte unsigned register[SRC_CHANNELS][4]);
        sc_table = st;
        this.register = register;
        for (int i = 0; i < SRC_CHANNELS; i++) begin
            if (OPT_MODE == 0) begin
                ch_cnt[i] = register[i][1];
            end else begin
                ch_cnt[i] = 0;
            end
        end
    endfunction

    virtual task pre_tx(ref Transaction transaction, string inst);
    endtask

    virtual task post_tx(Transaction transaction, string inst);
        MvbTransaction #(NEW_RX_ITEM_WIDTH) mvb_tr;
        MvbTransaction #(NEW_TX_ITEM_WIDTH) mvb_tr_ext = new();
        logic [ITEM_WIDTH-1 : 0] data;
        int channel;
        int channel_out;
        int ch_diff;
        $cast(mvb_tr, transaction);

        if(VERBOSE >= 1) begin
            $write("In transaction: \n");
            mvb_tr.display();
        end

        data = mvb_tr.data[ITEM_WIDTH+math_pkg::log2(SRC_CHANNELS)-1 : math_pkg::log2(SRC_CHANNELS)];
        channel = unsigned'(mvb_tr.data[math_pkg::log2(SRC_CHANNELS)-1 : 0]);

        if(VERBOSE >= 2) begin
            $write("In Data: %u\n", data);
            $write("In Channel: %u\n", channel);
        end
        if(VERBOSE >= 3) begin
            $write("Counter values are: \n");
            for (int i = 0; i < SRC_CHANNELS; i++) begin
                $write("Counter: %u\n", ch_cnt[i]);
            end
        end
        if(VERBOSE >= 4) begin
            $write("Information in register: \n");
            $write("Reg increment: %u\n", register[channel][0]);
            $write("Min channel: %u\n", register[channel][1]);
            $write("Max channel: %u\n", register[channel][2]);
            $write("Open space: %u\n", register[channel][3]);
        end

        if(register[channel][2] > DST_CHANNELS) begin
            $write("Max value of dst channel in register is higher than maximal channel");
            $write("Max channel: %u\n", register[channel][2]);
            $write("\n");
            $write("Max channel: %u\n", DST_CHANNELS);
            $stop;
        end
        if(register[channel][1] > DST_CHANNELS || register[channel][1] > register[channel][2]) begin
            $write("Min value of dst channel in register is higher than maximal channel or than max channel in register");
            $stop;
        end


        if(register[channel][0] == 0) begin
            ch_cnt[channel] = channel;
            channel_out = ch_cnt[channel];
        end
        else if(register[channel][0] > 0) begin
            if(OPT_MODE == 1) begin
                channel_out = ch_cnt[channel] + register[channel][1];
                if(VERBOSE >= 3) begin
                    $write("Counter before: %u\n", ch_cnt[channel]);
                end
                ch_diff = (register[channel][2] - register[channel][1]);
                $write("chan diff: %u\n", ch_diff);
                ch_cnt[channel] = (ch_cnt[channel] + register[channel][0]) & (ch_diff);
                if(VERBOSE >= 3) begin
                    $write("Counter after: %u\n", ch_cnt[channel]);
                end
            end
            if(OPT_MODE == 0) begin
                channel_out = ch_cnt[channel];
                if((ch_cnt[channel] + register[channel][0]) <= register[channel][2] && (ch_cnt[channel] + register[channel][0]) < DST_CHANNELS && (ch_cnt[channel] + register[channel][0]) >= register[channel][1]) begin
                    if(VERBOSE >= 3) begin
                        $write("Counter in if: %u\n", ch_cnt[channel]);
                    end
                    ch_cnt[channel] += register[channel][0];
                end else begin
                    if(VERBOSE >= 3) begin
                        $write("Counter in else: %u\n", ch_cnt[channel]);
                    end
                    ch_cnt[channel] = register[channel][1];
                end
            end
        end

        mvb_tr_ext.data[ITEM_WIDTH-1 : 0] = data;
        mvb_tr_ext.data[ITEM_WIDTH+math_pkg::log2(DST_CHANNELS)-1 : ITEM_WIDTH] = channel_out;

        if(VERBOSE >= 2) begin
            $write("Out Data: %u\n", data);
            $write("Out Channel: %u\n", channel_out);
        end

        if(VERBOSE >= 1) begin
            $write("Out transaction: \n");
            mvb_tr_ext.display();
            $write("\n");
        end

        sc_table.add(mvb_tr_ext);
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

        if(VERBOSE >= 1) begin
            $write("Transaction in check: \n");
            transaction.display();
        end

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

    function new (byte unsigned register[SRC_CHANNELS][4]);
      scoreTable = new;
      monitorCbs = new(scoreTable);
      driverCbs  = new(scoreTable, register);
    endfunction

    task display();
      scoreTable.display();
    endtask

endclass
