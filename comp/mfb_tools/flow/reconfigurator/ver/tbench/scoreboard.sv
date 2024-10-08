// scoreboard.sv: MFB Scoreboard
// Copyright (C) 2020 CESNET
// Author: Tomas Hak <xhakto01@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

import sv_common_pkg::*;
import sv_mfb_pkg::*;
import test_pkg::*;

class ScoreboardDriverCbs extends DriverCbs;

    TransactionTable #(0) sc_table;

    function new (TransactionTable #(0) st);
        sc_table = st;
    endfunction

    virtual task pre_tx(ref Transaction transaction, string inst);
       MfbTransaction #(RX_ITEM_WIDTH,META_WIDTH) rx_tr;
       $cast(rx_tr, transaction);
       rx_tr.meta[32-1:0] = rx_tr.data.size; // add original transaction size to metadata
       $cast(transaction,rx_tr);
    endtask

    virtual task post_tx(Transaction transaction, string inst);
       MfbTransaction #(RX_ITEM_WIDTH,META_WIDTH) rx_tr;
       MfbTransaction #(TX_ITEM_WIDTH,META_WIDTH) tx_tr;
       int tx_tr_size;
       $cast(rx_tr, transaction);
       tx_tr = new;
       tx_tr.meta = rx_tr.meta;
       tx_tr_size = rx_tr.data.size*RX_ITEM_WIDTH/TX_ITEM_WIDTH;
       if (RX_ITEM_WIDTH<TX_ITEM_WIDTH) begin
          // round up
          if (tx_tr_size*TX_ITEM_WIDTH!=rx_tr.data.size*RX_ITEM_WIDTH)
              tx_tr_size += 1;
          rx_tr.data = new [tx_tr_size*TX_ITEM_WIDTH/RX_ITEM_WIDTH] (rx_tr.data);
       end
       tx_tr.data = new [tx_tr_size];
       //for (int i=0;i<tx_tr.data.size;i++) begin
       //    tx_tr.data[i] =
       //end
       tx_tr.data = {<<TX_ITEM_WIDTH{{<<RX_ITEM_WIDTH{rx_tr.data}}}};
       sc_table.add(tx_tr);
    endtask

endclass



class ScoreboardMonitorCbs extends MonitorCbs;

    TransactionTable #(0) sc_table;

    function new (TransactionTable #(0) st);
        this.sc_table = st;
    endfunction

    virtual task post_rx(Transaction transaction, string inst);
        bit status=0;
        int orig_size;
        int target_size;
        int inv_bits;
        bit [TX_ITEM_WIDTH-1 : 0] last_item;
        MfbTransaction #(TX_ITEM_WIDTH,META_WIDTH) tx_tr;
        $cast(tx_tr, transaction);
        orig_size = tx_tr.meta;
        orig_size *= RX_ITEM_WIDTH;
        target_size = tx_tr.data.size*TX_ITEM_WIDTH;
        inv_bits = target_size-orig_size;
        // Fill invalid bits with 0s if needed
        if (orig_size!=target_size) begin
            for (int i=TX_ITEM_WIDTH-inv_bits;i<TX_ITEM_WIDTH;i++)
                tx_tr.data[tx_tr.data.size-1][i] = 0;
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
    endtask

endclass



class Scoreboard;

    TransactionTable #(0) scoreTable;
    ScoreboardMonitorCbs  monitorCbs;
    ScoreboardDriverCbs   driverCbs;

    function new ();
      scoreTable = new;
      monitorCbs = new(scoreTable);
      driverCbs  = new(scoreTable);
    endfunction

    task display();
      scoreTable.display();
    endtask

endclass

