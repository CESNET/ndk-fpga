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
import sv_mvb_pkg::*;

class ScoreboardDriverCbs extends DriverCbs;
   mailbox mfb_mailbox;

   function new (mailbox mbx);
      this.mfb_mailbox = mbx;
   endfunction

   virtual task pre_tx(ref Transaction transaction, string inst);
   endtask

   virtual task post_tx(Transaction transaction, string inst);
      if (FULL_PRINT) begin
         $write("MFB Transaction put to mailbox.\n");
         $write("Time: %t\n", $time);
         transaction.display();
      end
      mfb_mailbox.put(transaction);
   endtask
endclass

class ScoreboardFdMonitorCbs extends MonitorCbs;
   mailbox fd_mailbox;

   function new (mailbox mbx);
      this.fd_mailbox = mbx;
   endfunction

   virtual task post_rx(Transaction transaction, string inst);
      if (FULL_PRINT) begin
         $write("FD Transaction put to mailbox.\n");
         transaction.display();
      end
      fd_mailbox.put(transaction);
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
      if (FULL_PRINT) begin
         $write("Transaction received.\n");
         $write("Time: %t\n", $time);
         transaction.display();
      end
   endtask
endclass

class ScoreboardModel;
   bit enabled;
   mailbox MfbMbx;
   mailbox FdMbx;
   TransactionTable #(TR_TABLE_FIRST_ONLY) ScTable;

   function new (mailbox InMfbMbx, mailbox InFdMbx, TransactionTable #(TR_TABLE_FIRST_ONLY) InScTable);
      this.MfbMbx  = InMfbMbx;
      this.FdMbx   = InFdMbx;
      this.ScTable = InScTable;
      this.enabled = 0;
   endfunction

   task setEnabled();
      enabled = 1; // Model Enabling
      fork
         run(); // Creating model subprocess
      join_none; // Don't wait for ending
    endtask : setEnabled

   task setDisabled();
      enabled = 0; // Disable model
   endtask : setDisabled

   task run();
      Transaction MfbTr;
      Transaction FdTr;
      MfbTransaction #(ITEM_WIDTH,1) MfbTrans;
      MvbTransaction #(1) FdTrans;

      while (enabled) begin
         // Wait for MFB Transaction
         MfbMbx.get(MfbTr);
         $cast(MfbTrans,MfbTr);

         // Wait for FD Transaction
         FdMbx.get(FdTr);
         $cast(FdTrans,FdTr);

         if (FULL_PRINT) begin
            $write("MODEL: Transaction checking... \n");
         end
         if ((MfbTrans.meta == 1) || (FdTrans.data == 1)) begin
            if (FULL_PRINT) begin
               $write("MODEL: Transaction discarded! \n");
            end
         end else begin
            if (FULL_PRINT) begin
               $write("MODEL: Transaction send! \n");
            end
            ScTable.add(MfbTr);
         end
      end
   endtask
endclass

class Scoreboard;
   TransactionTable #(TR_TABLE_FIRST_ONLY) scoreTable;
   mailbox                                 MfbMailbox;
   mailbox                                 FdMailbox;
   ScoreboardFdMonitorCbs                  fd_monitorCbs;
   ScoreboardMonitorCbs                    monitorCbs;
   ScoreboardDriverCbs                     driverCbs;
   ScoreboardModel                         model;

   function new ();
      scoreTable    = new;
      MfbMailbox    = new;
      FdMailbox     = new;
      fd_monitorCbs = new(FdMailbox);
      driverCbs     = new(MfbMailbox);
      monitorCbs    = new(scoreTable);
      model         = new(MfbMailbox,FdMailbox,scoreTable);
   endfunction

   task setEnabled();
      model.setEnabled();
   endtask

   task setDisabled();
      model.setDisabled();
   endtask

   task display();
      scoreTable.display();
   endtask
endclass
