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
      localparam int CUT_OFFSET_WIDTH = ($clog2(MAX_CUT_OFFSET) > 1) ? $clog2(MAX_CUT_OFFSET) : 1;

      MfbTransaction #(ITEM_WIDTH,CUT_OFFSET_WIDTH+1) tr;
      MfbTransaction #(ITEM_WIDTH,CUT_OFFSET_WIDTH+1) tr_cutted;
      int cut_offset = 0;
      int size_after_cut;

      $cast(tr, transaction);
      //$write("tr: \n");
      //tr.display();

      if (MAX_CUT_OFFSET == 1) begin
         cut_offset = tr.meta[1];
      end else if (MAX_CUT_OFFSET > 1) begin
         cut_offset = tr.meta[CUT_OFFSET_WIDTH:1];
      end
      //$write("Cut offser: %d\n", cut_offset);

      size_after_cut = tr.data.size() - CUTTED_ITEMS;
      //$write("New size: %d\n", size_after_cut);

      tr_cutted = new();
      tr_cutted.meta = tr.meta;


      if (tr.meta[0] == 1) begin
         tr_cutted.data = new[size_after_cut];
         // copy before cut data
         for (int i=0; i<cut_offset; i++) begin
            tr_cutted.data[i] = tr.data[i];
         end
         // copy after cut data
         for (int i=cut_offset; i<size_after_cut; i++) begin
            tr_cutted.data[i] = tr.data[i+CUTTED_ITEMS];
         end
      end else begin
         tr_cutted.data = tr.data;
      end

      //$write("tr_cutted: \n");
      //tr_cutted.display();
      sc_table.add(tr_cutted);
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

    function int unsigned done();
        return (scoreTable.empty() != 0);
    endfunction

   task display();
      scoreTable.display();
   endtask
endclass
