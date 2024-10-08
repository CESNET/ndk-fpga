/* \scoreboard.sv
 * \brief Verification scoreboard
 * \author Jakub Cabal <cabal@cesnet.cz>
 * \date 2018
 */
/*
 * Copyright (C) 2018 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

import sv_common_pkg::*;
import sv_mfb_pkg::*;

class ScoreboardDriverCbs extends DriverCbs;
   TransactionTable #(TR_TABLE_FIRST_ONLY) sc_table;

   function new (TransactionTable #(TR_TABLE_FIRST_ONLY) st);
      sc_table = st;
   endfunction

   virtual task pre_tx(ref Transaction transaction, string inst);
   endtask

   virtual task post_tx(Transaction transaction, string inst);
      MfbTransaction #(ITEM_WIDTH,1) tr;

      $cast(tr, transaction);
      if (tr.data.size() > 3) begin
         sc_table.add(tr);
      end

   endtask
endclass

class ScoreboardMonitorCbs extends MonitorCbs;
   TransactionTable #(TR_TABLE_FIRST_ONLY) sc_table;
   int rx_cnt = 0;

   function new (TransactionTable #(TR_TABLE_FIRST_ONLY) st);
      this.sc_table = st;
   endfunction

   virtual task post_rx(Transaction transaction, string inst);
      bit status=0;
      rx_cnt = rx_cnt + 1;
      sc_table.remove(transaction, status);
      if (status==0)begin
         $write("Unknown transaction received from monitor %s\n", inst);
         $timeformat(-9, 3, " ns", 8);
         $write("Time: %t\n", $time);
         transaction.display();
         sc_table.display();
         $stop;
      end;
      //$write("%d. Transaction received.\n", rx_cnt);
   endtask
endclass

class Scoreboard;
   TransactionTable #(TR_TABLE_FIRST_ONLY) scoreTable;
   ScoreboardMonitorCbs                    monitorCbs;
   ScoreboardDriverCbs                     driverCbs;

   function new ();
      scoreTable = new;
      monitorCbs = new(scoreTable);
      driverCbs  = new(scoreTable);
   endfunction

   task display();
      scoreTable.display();
   endtask
endclass
