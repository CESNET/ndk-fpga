// scoreboard.sv: TCAM Scoreboard
// Copyright (C) 2020 CESNET z. s. p. o.
// Author: Tomas Hak <xhakto01@stud.fit.vutbr.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

import sv_common_pkg::*;
import sv_wb_pkg::*;
import sv_mvb_pkg::*;

class tcam_model #(int DATA_WIDTH, int ITEMS);

    local bit [DATA_WIDTH-1 : 0] data[];
    local bit [DATA_WIDTH-1 : 0] mask[];
    local bit vld[];
    bit busy;

    function new();
        data = new[ITEMS];
        mask = new[ITEMS];
        vld  = new[ITEMS];
        busy = 0;
        for(int i = 0; i < ITEMS; i++) begin
            vld[i]  = 0;
        end
    endfunction

    function int record(bit [log2(ITEMS)-1 : 0] a);
        record = vld[a];
    endfunction

    function void write(bit [DATA_WIDTH-1 : 0] d, bit [DATA_WIDTH-1 : 0] m, bit [log2(ITEMS)-1 : 0] a);
        busy    = 1;
        data[a] = d;
        mask[a] = m;
        vld[a]  = 1;
        busy    = 0;
    endfunction

    function void read(bit [log2(ITEMS)-1 : 0] a, output bit [DATA_WIDTH-1 : 0] d, output bit [DATA_WIDTH-1 : 0] m);
        busy = 1;
        d    = data[a];
        m    = mask[a];
        busy = 0;
    endfunction

    function void match(bit [DATA_WIDTH-1 : 0] d, output bit [ITEMS-1 : 0] bmp, output bit hit);
        busy = 1;
        for(int i = 0; i < ITEMS; i++) begin
            if (FULL_PRINT == TRUE) begin
                $write("addr  : %d\n", i);
                $write("data  : %b\n", data[i]);
                $write("mask  : %b\n", mask[i]);
                $write("match : %b\n", d);
            end
            if (vld[i]) begin
                bmp[i] = (data[i] & mask[i]) == (d & mask[i]);
                if (FULL_PRINT == TRUE) begin
                    $write("is match : %b\n", bmp[i]);
                end
            end else begin
                bmp[i] = 0;
                if (FULL_PRINT == TRUE) begin
                    $write("is match : %b\n", bmp[i]);
                end
            end
        end
        hit = |bmp;
        if (FULL_PRINT == TRUE) begin
            $write("TOTAL match: %h\n\n", bmp);
        end
        busy = 0;
    endfunction
endclass


class ScoreboardWriteDriverCbs #(int DATA_WIDTH, int ITEMS, bit FRAGMENTED_MEM) extends DriverCbs;
    tcam_model #(DATA_WIDTH, ITEMS) tcam;

    function new(tcam_model #(DATA_WIDTH, ITEMS) tcam_i);
        this.tcam = tcam_i;
    endfunction

    virtual task pre_tx(ref Transaction transaction, string inst);
    endtask

    virtual task post_tx(Transaction transaction, string inst);
        //$write("Write transaction\n");
        WbTransaction #(DATA_WIDTH, log2(ITEMS), FRAGMENTED_MEM) tr;
        $cast(tr, transaction);
        if(FULL_PRINT == TRUE) begin
            $write("Write to TCAM model\n");
            tr.display();
        end
        wait(!tcam.busy);
        tcam.write(tr.data, tr.mask, tr.addr);
    endtask
endclass

class ScoreboardReadDriverCbs #(int DATA_WIDTH, int ITEMS) extends DriverCbs;
    tcam_model       #(DATA_WIDTH, ITEMS) tcam;
    TransactionTable #(0)                 sc_table;

    function new(tcam_model #(DATA_WIDTH, ITEMS) tcam_i, TransactionTable #(0) sc_table_i);
        this.tcam     = tcam_i;
        this.sc_table = sc_table_i;
    endfunction

    virtual task pre_tx(ref Transaction transaction, string inst);
    endtask

    virtual task post_tx(Transaction transaction, string inst);
        MvbTransaction #(log2(ITEMS)) tr;
        MvbTransaction #(2*DATA_WIDTH) read_out_tr;
        bit [DATA_WIDTH-1 : 0] read_data = {DATA_WIDTH{1'b0}};
        bit [DATA_WIDTH-1 : 0] read_mask = {DATA_WIDTH{1'b0}};

        //$write("Read transaction\n");
        $cast(tr, transaction);
        if(FULL_PRINT == TRUE) begin
            $write("Read from TCAM model\n");
            tr.display();
        end
        wait(!tcam.busy);
        if(tcam.record(tr.data)) begin
            tcam.read(tr.data, read_data, read_mask);
        end

        read_out_tr = new();
        read_out_tr.data[2*DATA_WIDTH-1 : DATA_WIDTH] = read_data;
        read_out_tr.data[  DATA_WIDTH-1 : 0]          = read_mask;

        sc_table.add(read_out_tr);
    endtask
endclass

class ScoreboardMatchDriverCbs #(int DATA_WIDTH, int ITEMS) extends DriverCbs;
    tcam_model       #(DATA_WIDTH,ITEMS) tcam;
    TransactionTable #(0)                sc_table;

    function new(tcam_model #(DATA_WIDTH, ITEMS) tcam_i, TransactionTable #(0) sc_table_i);
        this.tcam     = tcam_i;
        this.sc_table = sc_table_i;
    endfunction

    virtual task pre_tx(ref Transaction transaction, string inst);
    endtask

    virtual task post_tx(Transaction transaction, string inst);
        MvbTransaction #(DATA_WIDTH) tr;
        MvbTransaction #(ITEMS+1)    match_out_tr;
        bit [ITEMS-1 : 0]            match_out;
        bit                          match_out_hit;

        //$write("Match transaction\n");
        $cast(tr, transaction);
        if (FULL_PRINT == TRUE) begin
            $write("Match to TCAM model\n");
            tr.display();
        end
        wait(!tcam.busy);
        tcam.match(tr.data, match_out, match_out_hit);

        match_out_tr = new();
        match_out_tr.data[ITEMS-1 : 0] = match_out;
        match_out_tr.data[ITEMS]       = match_out_hit;

        sc_table.add(match_out_tr);
    endtask
endclass


class ScoreboardMonitorCbs extends MonitorCbs;
    TransactionTable #(0) sc_table;

    function new(TransactionTable #(0) sc_table_i);
        this.sc_table = sc_table_i;
    endfunction

    virtual task pre_rx(ref Transaction transaction, string inst);
    endtask

    virtual task post_rx(Transaction transaction, string inst);
        bit status = 0;
        sc_table.remove(transaction, status);
        if(status == 0) begin
            $write("Unknown transaction received from monitor %s\n", inst);
            $timeformat(-9, 3, " ns", 8);
            $write("Time: %t\n", $time);
            transaction.display();
            sc_table.display();
            $stop;
        end;
    endtask
endclass


class Scoreboard #(int DATA_WIDTH, int ITEMS, bit FRAGMENTED_MEM);

    ScoreboardWriteDriverCbs  #(DATA_WIDTH, ITEMS, FRAGMENTED_MEM) writeDriverCbs;
    ScoreboardReadDriverCbs   #(DATA_WIDTH, ITEMS) readDriverCbs;
    ScoreboardMatchDriverCbs  #(DATA_WIDTH, ITEMS) matchDriverCbs;
    ScoreboardMonitorCbs                           readMonitorCbs;
    ScoreboardMonitorCbs                           matchMonitorCbs;
    tcam_model                #(DATA_WIDTH,ITEMS)  tcam;
    TransactionTable          #(0)                 scoreTable;

    function new();
        tcam            = new();
        scoreTable      = new();
        readMonitorCbs  = new(scoreTable);
        matchMonitorCbs = new(scoreTable);
        writeDriverCbs  = new(tcam);
        readDriverCbs   = new(tcam, scoreTable);
        matchDriverCbs  = new(tcam, scoreTable);
    endfunction

    task display();
        scoreTable.display();
    endtask

endclass
