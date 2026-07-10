/* \scoreboard.sv
 * \brief Verification scoreboard
 * \author Jakub Cabal <cabal@cesnet.cz>
 * \date 2026
 */
/*
 * Copyright (C) 2026 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

import sv_common_pkg::*;
import sv_mfb_pkg::*;
import sv_mvb_pkg::*;


class ScoreboardDriverCbs extends DriverCbs;
   TransactionTable #(TR_TABLE_FIRST_ONLY) sc_table;

   function new (TransactionTable #(TR_TABLE_FIRST_ONLY) st);
      sc_table = st;
   endfunction

   virtual task pre_tx(ref Transaction transaction, string inst);
      // Not used because extraction is done on the received packet data.
   endtask

   virtual task post_tx(Transaction transaction, string inst);
      MfbTransaction #(ITEM_WIDTH) tr;
      MvbTransaction #(EXTRACTED_ITEMS*ITEM_WIDTH) ex_tr;
      int unsigned start_idx;
      int unsigned pkt_len;

      $cast(tr, transaction);
      ex_tr = new();

      pkt_len = tr.data.size();
      // Extract the last EXTRACTED_ITEMS, or the whole packet if shorter.
      if (pkt_len > EXTRACTED_ITEMS) begin
         start_idx = pkt_len - EXTRACTED_ITEMS;
      end else begin
         start_idx = 0;
      end

      for (int i=0; i<EXTRACTED_ITEMS; i++) begin
         if (start_idx + i < pkt_len) begin
            ex_tr.data[ITEM_WIDTH*i +: ITEM_WIDTH] = tr.data[start_idx + i];
         end else begin
            ex_tr.data[ITEM_WIDTH*i +: ITEM_WIDTH] = '0;
         end
      end

      sc_table.add(ex_tr);
   endtask
endclass


class ScoreboardMonitorCbs extends MonitorCbs;
   TransactionTable #(TR_TABLE_FIRST_ONLY) sc_table;

   function new (TransactionTable #(TR_TABLE_FIRST_ONLY) st);
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
