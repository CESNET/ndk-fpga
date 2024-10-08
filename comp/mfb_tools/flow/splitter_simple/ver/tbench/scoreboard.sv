/* \scoreboard.sv
 * \brief Verification scoreboard
 * \author Daniel Kondys <xkondy00@vutbr.cz>
 * \date 2019
 */
 /*
 * Copyright (C) 2019 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

import sv_common_pkg::*;
import sv_mfb_pkg::*;



class ScoreboardDriverCbs extends DriverCbs;

    TransactionTable #(0) sc_table0;
    TransactionTable #(0) sc_table1;

    function new (TransactionTable #(0) st0,TransactionTable #(0) st1);
        sc_table0 = st0;
        sc_table1 = st1;
    endfunction

    virtual task pre_tx(ref Transaction transaction, string inst);
    endtask

    virtual task post_tx(Transaction transaction, string inst);
        bit sel_bit;
        MfbTransaction #(ITEM_WIDTH) mfb_tr;

        $cast(mfb_tr, transaction);
        sel_bit = mfb_tr.meta[0];
        if (sel_bit == 1) begin
            //$write("\n Transaction for TX1 send by driver.\n");
            sc_table1.add(transaction);
        end else begin
            //$write("\n Transaction for TX0 send by driver.\n");
            sc_table0.add(transaction);
        end;
        //transaction.display();
    endtask

endclass



class ScoreboardMonitorCbs0 extends MonitorCbs;

    TransactionTable #(0) sc_table;
    int cnt = 0;

    function new (TransactionTable #(0) st);
        this.sc_table = st;
    endfunction

    virtual task post_rx(Transaction transaction, string inst);
        bit status=0;
        cnt = cnt + 1;
        sc_table.remove(transaction, status);
        if (status==0) begin
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
        //$write("Transaction OK - monitor 0 \n");
    endtask

endclass

class ScoreboardMonitorCbs1 extends MonitorCbs;

    TransactionTable #(0) sc_table;

    function new (TransactionTable #(0) st);
        this.sc_table = st;
    endfunction

    virtual task post_rx(Transaction transaction, string inst);
        bit status=0;
        sc_table.remove(transaction, status);
        if (status==0)begin
            $write("Unknown transaction received from monitor %s\n", inst);
            $timeformat(-9, 3, " ns", 8);
            $write("Time: %t\n", $time);
            transaction.display();
            sc_table.display();
            $stop;
        end;
        //$write("Transaction OK - monitor 1 \n");
    endtask

endclass


class Scoreboard;

    TransactionTable #(0) scoreTable0;
    TransactionTable #(0) scoreTable1;
    ScoreboardMonitorCbs0 monitorCbs0;
    ScoreboardMonitorCbs1 monitorCbs1;
    ScoreboardDriverCbs   driverCbs;

    function new ();
      scoreTable0 = new;
      scoreTable1 = new;
      monitorCbs0 = new(scoreTable0);
      monitorCbs1 = new(scoreTable1);
      driverCbs   = new(scoreTable0, scoreTable1);
    endfunction

    task display();
      scoreTable0.display();
      scoreTable1.display();
    endtask

endclass
