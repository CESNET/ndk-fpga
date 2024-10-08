// wb_driver.sv: Write Bus interface Driver
// Copyright (C) 2020 CESNET z. s. p. o.
// Author: Tomas Hak <xhakto01@stud.fit.vutbr.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

class WbDriver #(DATA_WIDTH = 64, ADDR_WIDTH = 8, FRAGMENTED_MEM = FALSE) extends Driver;

    protected virtual iWbRx#(DATA_WIDTH,ADDR_WIDTH).tb vif;
    protected bit [DATA_WIDTH-1 : 0] data;
    protected bit [DATA_WIDTH-1 : 0] mask;
    protected bit [ADDR_WIDTH-1 : 0] addr;

    protected bit src_rdy;
    protected int unsigned word;

    rand bit wordDelayEn;
    int wordDelayEnable_wt = 0;
    int wordDelayDisable_wt = 1;
    rand integer wordDelay;
    int wordDelayLow = 0;
    int wordDelayHigh = 0;

    constraint cDelays{
        wordDelayEn dist {1'b1 := wordDelayEnable_wt, 1'b0 := wordDelayDisable_wt};
        wordDelay inside { [wordDelayLow:wordDelayHigh] };
    }


    function new(string i, tTransMbx t, virtual iWbRx#(DATA_WIDTH,ADDR_WIDTH).tb v);
        super.new(i, t);
        vif = v;
        src_rdy = 0;
    endfunction

    task moveWord();
        vif.cb.DATA <= data;
        vif.cb.MASK <= mask;
        vif.cb.ADDR <= addr;
        vif.cb.SRC_RDY <= src_rdy;
        if(src_rdy) begin
            do
                @(vif.cb);
            while(!vif.cb.DST_RDY);
            vif.cb.SRC_RDY <= 0;
            IDLE_RANDOMIZE : assert(randomize());
            if(wordDelayEn)
                repeat(wordDelay)
                    @(vif.cb);
        end else begin
            @(vif.cb);
        end
        src_rdy = 0;
    endtask

    task run();
        Transaction transaction;
        WbTransaction #(DATA_WIDTH, ADDR_WIDTH, FRAGMENTED_MEM) tr;
        @(vif.cb); // initial sync
        while(enabled) begin
            while(transMbx.try_get(transaction) == 0) begin // wait for transaction
                moveWord();
                busy = 0;
                if (!enabled) return;
            end
            busy = 1;

            foreach(cbs[i]) cbs[i].pre_tx(transaction, inst); // notify callbacks
            $cast(tr, transaction);
            data = tr.data;
            mask = tr.mask;
            addr = tr.addr;
            src_rdy = 1;
            foreach(cbs[i]) cbs[i].post_tx(transaction, inst);
            moveWord();
        end
    endtask

endclass
