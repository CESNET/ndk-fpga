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
import test_pkg::*;

class ScoreboardGeneratorCbs;
   TransactionTable #(1) sc_table;

   function new (TransactionTable #(1) st);
      sc_table = st;
   endfunction

   virtual task post_gen(Transaction transaction);
      sc_table.add(transaction);
   endtask
endclass

class ScoreboardMonitorCbs extends MonitorCbs;
   TransactionTable #(1) sc_table;
   int cnt = 0;

   function new (TransactionTable #(1) st);
      this.sc_table = st;
   endfunction

   virtual task post_rx(Transaction transaction, string inst);
      CustomTransaction #(HDR_WIDTH,MFB_ITEM_WIDTH) custom_tr;
      bit status=0;
      // MFB to Custom transaction
      custom_tr = new();
      mfb2custom(transaction,custom_tr);
      cnt = cnt + 1;
      // Compare custom transaction and remove from table
      sc_table.remove(custom_tr, status);
      if (status==0) begin
         //transaction.display();
         $write("=============================================================\n");
         $write("UNKNOWN transaction received from monitor %s\n", inst);
         $write("=============================================================\n");
         $timeformat(-9, 3, " ns", 8);
         $write("Time: %t\n", $time);
         custom_tr.display();
         sc_table.display();
         $stop;
      end;
      //$write("=============================================================\n");
      //$write("%0d. transaction received from monitor %s\n", cnt, inst);
      //$write("=============================================================\n");
      //custom_tr.display();
   endtask

   virtual task mfb2custom(Transaction tr, CustomTransaction #(HDR_WIDTH,MFB_ITEM_WIDTH) custom_tr);
      MfbTransaction    #(MFB_ITEM_WIDTH)  mfb_tr;
      int payload_len = 0;

      $cast(mfb_tr, tr);

      // convert header
      for (int i=0; i < HDR_SIZE; i++) begin
         custom_tr.header[(i*MFB_ITEM_WIDTH)+:MFB_ITEM_WIDTH] = mfb_tr.data[i];
      end

      // convert payload
      if (mfb_tr.data.size() == HDR_SIZE) begin
         custom_tr.payload_en = 0;
      end else begin
         custom_tr.payload_en = 1;
         //$write("TRANSACTION WITH PAYLOAD!");
         payload_len = mfb_tr.data.size() - HDR_SIZE;
         // resize payload
         custom_tr.payload = new[payload_len];
         for (int i=0; i < payload_len; i++) begin
            custom_tr.payload[i] = mfb_tr.data[(i+HDR_SIZE)];
         end
      end
   endtask
endclass

class Scoreboard;
   TransactionTable #(1)  scoreTable;
   ScoreboardGeneratorCbs generatorCbs;
   ScoreboardMonitorCbs   monitorCbs;

   function new ();
      scoreTable   = new;
      generatorCbs = new(scoreTable);
      monitorCbs   = new(scoreTable);
   endfunction

   task display();
      scoreTable.display();
   endtask
endclass
