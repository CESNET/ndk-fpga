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

class ScoreboardGeneratorCbs;
   TransactionTable #(1) sc_table[SPLITTER_OUTPUTS-1:0];

   function new (TransactionTable #(1) st[SPLITTER_OUTPUTS-1:0]);
      sc_table = st;
   endfunction

   virtual task post_gen(Transaction transaction);
      CustomTransaction #(HDR_SIZE,MFB_ITEM_WIDTH) custom_tr;
      $cast(custom_tr, transaction);

      if (FULL_PRINT) begin
         $write("POST GEN: TRANSACTION FOR PORT %d!\n", custom_tr.switch);
         custom_tr.display();
      end
      sc_table[custom_tr.switch].add(transaction);
   endtask
endclass

class ScoreboardMvbMonitorCbs extends MonitorCbs;
   mailbox mvbMbx;

   function new (mailbox fMbx);
      mvbMbx = fMbx;
   endfunction

   virtual task post_rx(Transaction transaction, string inst);
      MvbTransaction #(HDR_WIDTH) mvb_tr;

      if (FULL_PRINT) begin
         $write("Monitor MVB: GET TRANSACTION!\n");
      end
      $cast(mvb_tr,transaction);
      mvbMbx.put(mvb_tr);
   endtask
endclass

class ScoreboardMfbMonitorCbs extends MonitorCbs;
   mailbox mfbMbx;

   function new (mailbox fMbx);
      mfbMbx = fMbx;
   endfunction

   virtual task post_rx(Transaction transaction, string inst);
      MfbTransaction #(MFB_ITEM_WIDTH) mfb_tr;

      if (FULL_PRINT) begin
         $write("Monitor MFB: GET TRANSACTION!\n");
      end
      $cast(mfb_tr,transaction);
      mfbMbx.put(mfb_tr);
   endtask
endclass

class Checker;
   bit                   enabled;
   TransactionTable #(1) sc_table;
   mailbox               mfbMbx;
   mailbox               mvbMbx;
   int                   index;

   function new (TransactionTable #(1) st, mailbox fMbx, mailbox vMbx, int ind);
      sc_table = st;
      mfbMbx   = fMbx;
      mvbMbx   = vMbx;
      index    = ind;
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
      int cnt = 0;
      MvbTransaction #(HDR_WIDTH) mvb_tr;
      MfbTransaction #(MFB_ITEM_WIDTH) mfb_tr;
      CustomTransaction #(HDR_SIZE,MFB_ITEM_WIDTH) custom_tr;

      while (enabled) begin // Repeat while enabled
         status = 0;

         custom_tr = new();
         mvbMbx.get(mvb_tr);

         if (mvb_tr.data[0]) begin // header with payload
            mfbMbx.get(mfb_tr);
            // copy header
            custom_tr.hdr = mvb_tr.data;
            // add payload
            custom_tr.payload = 1;
            // add switch
            custom_tr.switch = index;
            // copy payload data
            custom_tr.data = new[mfb_tr.data.size()];
            for (int i=0; i < custom_tr.data.size(); i++) begin
               custom_tr.data[i] = mfb_tr.data[i];
            end
         end else begin // header without payload
            // copy header
            custom_tr.hdr = mvb_tr.data;
            // add payload
            custom_tr.payload = 0;
            // add switch
            custom_tr.switch = index;
         end

         if (FULL_PRINT) begin
            $write("CHECKER %0d: CUSTOM TRANSACTION:", index);
            custom_tr.display();
         end

         // check
         cnt = cnt + 1;
         sc_table.remove(custom_tr, status);
         if (status==0) begin
            $write("Unknown transaction in checker %0d\n", index);
            $timeformat(-9, 3, " ns", 8);
            $write("Time: %t\n", $time);
            custom_tr.display();
            sc_table.display();
            $stop;
         end;
         if ((cnt % 5000) == 0) begin
            $write("PORT%0d: %0d transactions received.\n", index, cnt);
         end;
      end
   endtask
endclass

class Scoreboard;
   TransactionTable #(1)   scoreTable[SPLITTER_OUTPUTS-1:0];
   ScoreboardGeneratorCbs  generatorCbs;
   ScoreboardMvbMonitorCbs mvbMonitorCbs[SPLITTER_OUTPUTS-1:0];
   ScoreboardMfbMonitorCbs mfbMonitorCbs[SPLITTER_OUTPUTS-1:0];
   Checker                 dutCheck[SPLITTER_OUTPUTS-1:0];
   mailbox                 mvbMbx[SPLITTER_OUTPUTS-1:0];
   mailbox                 mfbMbx[SPLITTER_OUTPUTS-1:0];

   function new ();
      for (int i = 0; i < SPLITTER_OUTPUTS; i++) begin
         scoreTable[i]    = new;
         mvbMbx[i]        = new;
         mfbMbx[i]        = new;
         mvbMonitorCbs[i] = new(mvbMbx[i]);
         mfbMonitorCbs[i] = new(mfbMbx[i]);
         dutCheck[i]      = new(scoreTable[i],mfbMbx[i],mvbMbx[i],i);
      end
      generatorCbs = new(scoreTable);

   endfunction

   task setEnabled();
      for (int i = 0; i < SPLITTER_OUTPUTS; i++) begin
         dutCheck[i].setEnabled();
      end
   endtask

   task setDisabled();
      for (int i = 0; i < SPLITTER_OUTPUTS; i++) begin
         dutCheck[i].setDisabled();
      end
   endtask

   task display();
      for (int i = 0; i < SPLITTER_OUTPUTS; i++) begin
         scoreTable[i].display();
      end
   endtask
endclass
