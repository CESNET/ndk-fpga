/*!
 * \file mvb_monitor.sv
 * \brief Monitor of Multi-Value Bus
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2016
 */
 /*
 * Copyright (C) 2016 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */



class MvbMonitor #(ITEMS = 4, ITEM_WIDTH = 8) extends Monitor;

    local virtual iMvbTx#(ITEMS,ITEM_WIDTH).monitor vif;
    protected int unsigned word;

    function new(string i, virtual iMvbTx#(ITEMS,ITEM_WIDTH).monitor v);
        super.new(i);
        vif = v;
        word = 0;
    endfunction

    virtual task run();
        Transaction transaction;
        MvbTransaction #(ITEM_WIDTH) tr;
        while(enabled) begin
            do begin
                @(vif.monitor_cb);
                busy = vif.monitor_cb.SRC_RDY;
                if(!enabled) return;
            end while(!(vif.monitor_cb.SRC_RDY && vif.monitor_cb.DST_RDY)); // wait for valid data
            if(!vif.monitor_cb.VLD) begin
                $write("@%0t - %s: Error in MVB protocol! Valid word without a single valid item.\n", $time, inst);
                @(vif.monitor_cb);
                $stop();
            end else
                for(int j=0; j < ITEMS; j++)
                    if(vif.monitor_cb.VLD[j]) begin
                        tr = new;
                        $cast(transaction, tr);
                        foreach(cbs[i]) cbs[i].pre_rx(transaction, inst);
                        tr.data = vif.monitor_cb.DATA[j*ITEM_WIDTH+:ITEM_WIDTH];
                        tr.stream = j;
                        tr.word = word;
                        foreach(cbs[i]) cbs[i].post_rx(transaction, inst);
                    end
            word = word + 1;
        end
    endtask

endclass
