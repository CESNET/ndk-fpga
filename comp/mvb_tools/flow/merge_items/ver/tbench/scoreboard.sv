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

class ScoreboardDriverCbs extends DriverCbs;

    TransactionTable #(0) sc_table;

    function new (TransactionTable #(0) st);
        sc_table = st;
    endfunction

    virtual task pre_tx(ref Transaction transaction, string inst);
    endtask

    virtual task post_tx(Transaction transaction, string inst);
        sc_table.add(transaction);
    endtask

endclass



class ScoreboardMonitorCbs extends MonitorCbs;

    TransactionTable #(0) sc_table0;
    TransactionTable #(0) sc_table1;

    function new (TransactionTable #(0) st0, TransactionTable #(0) st1);
        this.sc_table0 = st0;
        this.sc_table1 = st1;
    endfunction

    virtual task post_rx(Transaction transaction, string inst);
        bit status=0;
        MvbTransaction #(RX0_ITEM_WIDTH+RX1_ITEM_WIDTH) tx_tr;
        MvbTransaction #(RX0_ITEM_WIDTH) rx0_tr = new();
        MvbTransaction #(RX1_ITEM_WIDTH) rx1_tr = new();
        $cast(tx_tr, transaction);

        rx0_tr.data = tx_tr.data[RX0_ITEM_WIDTH-1:0];
        rx1_tr.data = tx_tr.data[RX0_ITEM_WIDTH+RX1_ITEM_WIDTH-1:RX0_ITEM_WIDTH];

        sc_table0.remove(rx0_tr, status);
        if (status==0)begin
            $write("Unknown RX0 transaction received from monitor %s\n", inst);
            $timeformat(-9, 3, " ns", 8);
            $write("Time: %t\n", $time);
            rx0_tr.display();
            sc_table0.display();
            $stop;
        end;
        sc_table1.remove(rx1_tr, status);
        if (status==0)begin
            $write("Unknown RX1 transaction received from monitor %s\n", inst);
            $timeformat(-9, 3, " ns", 8);
            $write("Time: %t\n", $time);
            rx1_tr.display();
            sc_table1.display();
            $stop;
        end;
    endtask

endclass



class Scoreboard;

    TransactionTable #(0) scoreTable0;
    TransactionTable #(0) scoreTable1;
    ScoreboardMonitorCbs  monitorCbs;
    ScoreboardDriverCbs   driverCbs0;
    ScoreboardDriverCbs   driverCbs1;

    function new ();
        scoreTable0 = new;
        scoreTable1 = new;
        monitorCbs  = new(scoreTable0, scoreTable1);
        driverCbs0  = new(scoreTable0);
        driverCbs1  = new(scoreTable1);
    endfunction

    task display();
        scoreTable0.display();
        scoreTable1.display();
    endtask

endclass
