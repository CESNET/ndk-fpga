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

parameter SC_TABLE_MODE = 0;

class ScoreboardGeneratorCbs;
   TransactionTable #(SC_TABLE_MODE) sc_table;

   function new (TransactionTable #(SC_TABLE_MODE) st);
      sc_table = st;
   endfunction

   virtual task post_gen(Transaction transaction);
      CustomTransaction #(MVB_ITEM_WIDTH,MFB_ITEM_WIDTH,MFB_META_WIDTH) custom_tr;
      $cast(custom_tr, transaction);

      if (FULL_PRINT) begin
         $timeformat(-9, 3, " ns", 8);
         $write("Time: %t\n", $time);
         $write("POST GEN: TRANSACTION FOR PORT %d!\n", custom_tr.switch);
         custom_tr.display();
      end
      sc_table.add(transaction);
   endtask
endclass

class ScoreboardMonitorCbs extends MonitorCbs;
   mailbox mfbMbx;
   mailbox mvbMbx;

   function new (mailbox fMbx, mailbox vMbx);
      mfbMbx = fMbx;
      mvbMbx = vMbx;
   endfunction

   virtual task post_rx(Transaction transaction, string inst);
      MvbTransaction #(MVB_ITEM_WIDTH) mvb_tr;
      MfbTransaction #(MFB_ITEM_WIDTH,MFB_META_WIDTH) mfb_tr;

      if (inst == "Monitor MVB") begin
         $cast(mvb_tr,transaction);
         if (FULL_PRINT) begin
            $write("Monitor MVB: GET TRANSACTION!\n");
            mvb_tr.display();
         end
         mvbMbx.put(mvb_tr);
      end else if (inst == "Monitor MFB") begin
         $cast(mfb_tr,transaction);
         if (FULL_PRINT) begin
            $write("Monitor MFB: GET TRANSACTION!\n");
            mfb_tr.display();
         end
         mfbMbx.put(mfb_tr);
      end else begin
         $write("VERIFICATION FAILED! BUG IN MONITOR CONFIGURATION?\n");
         $stop;
      end
   endtask
endclass

class Checker;
   bit                      enabled;
   TransactionTable #(SC_TABLE_MODE) sc_table;
   mailbox                  mfbMbx;
   mailbox                  mvbMbx;

   function new (TransactionTable #(SC_TABLE_MODE) st, mailbox fMbx, mailbox vMbx);
      sc_table = st;
      mfbMbx   = fMbx;
      mvbMbx   = vMbx;
   endfunction

   task setEnabled();
      enabled = 1; // Model Enabling
      fork
         run(); // Creating model subprocess
      join_none; // Don't wait for ending
   endtask

   task setDisabled();
      enabled = 0; // Disable model
   endtask

   task run();
      bit status = 0;
      int lenght = 0;
      int cnt = 0;
      MvbTransaction #(MVB_ITEM_WIDTH) mvb_tr;
      MfbTransaction #(MFB_ITEM_WIDTH,MFB_META_WIDTH) mfb_tr;
      CustomTransaction #(MVB_ITEM_WIDTH,MFB_ITEM_WIDTH,MFB_META_WIDTH) custom_tr;

      while (enabled) begin // Repeat while enabled
         status = 0;

         custom_tr = new();
         mvbMbx.get(mvb_tr);

         //if (FULL_PRINT) begin
         //   $write("CHECKER: MVB TRANSACTION:");
         //   mvb_tr.display();
         //end

        // copy header
        custom_tr.hdr = mvb_tr.data;
        // add payload
        custom_tr.payload = mvb_tr.data[0];
        // add switch
        custom_tr.switch = mvb_tr.data[4];

         if (custom_tr.payload) begin // header with payload
            mfbMbx.get(mfb_tr);
            // copy payload data
            custom_tr.data = new[mfb_tr.data.size()];
            for (int i=0; i < custom_tr.data.size(); i++) begin
               custom_tr.data[i] = mfb_tr.data[i];
            end
            // copy payload metadata
            custom_tr.meta = mfb_tr.meta;
         end

         if (FULL_PRINT) begin
            $write("CHECKER: CUSTOM TRANSACTION:");
            custom_tr.display();
         end

         // check
         cnt = cnt + 1;
         sc_table.remove(custom_tr, status);
         if (status==0) begin
            $write("Unknown transaction in checker\n");
            $timeformat(-9, 3, " ns", 8);
            $write("Time: %t\n", $time);
            custom_tr.display();
            sc_table.display();
            $stop;
         end;
         if ((cnt % 1000) == 0) begin
            $write("%0d transactions received.\n", cnt);
         end;
      end
   endtask
endclass

class Scoreboard;
   TransactionTable #(SC_TABLE_MODE) scoreTable;
   ScoreboardGeneratorCbs generatorCbs;
   ScoreboardMonitorCbs   monitorCbs;
   Checker                dutCheck;
   mailbox                mvbMbx;
   mailbox                mfbMbx;

   function new ();
      scoreTable   = new;
      mvbMbx       = new;
      mfbMbx       = new;
      generatorCbs = new(scoreTable);
      monitorCbs   = new(mfbMbx,mvbMbx);
      dutCheck     = new(scoreTable,mfbMbx,mvbMbx);
   endfunction

   task setEnabled();
      dutCheck.setEnabled();
   endtask

   task setDisabled();
      dutCheck.setDisabled();
   endtask

   task display();
      scoreTable.display();
   endtask
endclass
