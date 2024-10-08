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
import sv_mvb_pkg::*;
import sv_mfb_pkg::*;
import test_pkg::*;

class ScoreboardDriverCbs extends DriverCbs;
   TransactionTable #(1) sc_table;

   function new (TransactionTable #(1) st);
      sc_table = st;
   endfunction

   virtual task pre_tx(ref Transaction transaction, string inst);
      MvbTransaction #(LEN_WIDTH) mvb_tr;
      $cast(mvb_tr,transaction);
      if (mvb_tr.data > 59) begin
         mvb_tr.data = mvb_tr.data;
      end else begin
         mvb_tr.data = 60;
      end
      $cast(transaction,mvb_tr);
   endtask

   virtual task post_tx(Transaction transaction, string inst);
      MvbTransaction #(LEN_WIDTH) mvb_tr;
      MfbTransaction #(ITEM_WIDTH) mfb_tr;
      Transaction gen_tr;
      int length;

      $cast(mvb_tr,transaction);
      length = mvb_tr.data;
      // create MFB trans
      mfb_tr = new();
      mfb_tr.data = new[length];
      $cast(gen_tr,mfb_tr);
      sc_table.add(gen_tr);
   endtask

endclass

class ScoreboardMonitorCbs extends MonitorCbs;
   TransactionTable #(1) sc_table;
   int cnt = 0;

   function new (TransactionTable #(1) st);
      this.sc_table = st;
   endfunction

   virtual task post_rx(Transaction transaction, string inst);
      bit status=0;
      cnt = cnt + 1;
      // Compare custom transaction and remove from table
      sc_table.remove(transaction, status);
      if (status==0) begin
         $write("=============================================================\n");
         $write("UNKNOWN transaction received from monitor %s\n", inst);
         $write("=============================================================\n");
         $timeformat(-9, 3, " ns", 8);
         $write("Time: %t\n", $time);
         transaction.display();
         sc_table.display();
         $stop;
      end;
      //$write("=============================================================\n");
      //$write("%0d. transaction received from monitor %s\n", cnt, inst);
      //$write("=============================================================\n");
      //transaction.display();
   endtask
endclass

class Scoreboard;
   TransactionTable #(1)  scoreTable;
   ScoreboardDriverCbs    driverCbs;
   ScoreboardMonitorCbs   monitorCbs;

   function new ();
      scoreTable = new;
      driverCbs  = new(scoreTable);
      monitorCbs = new(scoreTable);
   endfunction

   task display();
      scoreTable.display();
   endtask
endclass
