/* \scoreboard.sv
 * \brief Verification scoreboard
 * \author Jakub Cabal <xcabal05@stud.feec.vutbr.cz>
 * \date 2017
 */
 /*
 * Copyright (C) 2017 CESNET z. s. p. o.
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
       sc_table0.add(transaction);
       sc_table1.add(transaction);
    endtask

endclass



class ScoreboardMonitorCbs0 extends MonitorCbs;

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
