/*
 * custom_trans_gen.sv: Custom transaction generator
 * Copyright (C) 2018 CESNET z. s. p. o.
 * Author(s): Jakub Cabal <cabal@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

//import sv_common_pkg::*;
import sv_mvb_pkg::*;
import sv_mfb_pkg::*;
import test_pkg::*;

class CustomTransGenerator;
   string inst;                      // Generator Identifier
   bit enabled;                      // Generator enabled
   ScoreboardGeneratorCbs cbs;
   tTransMbx mvbTransMbx;
   tTransMbx mfbTransMbx;

   int unsigned stopAfterTransCount; // Generator will stop after specified number of transactions
   protected int data_id;            // Transaction counter

   Transaction blueprint;

   function new (string inst);
      this.mvbTransMbx = new(10);
      this.mfbTransMbx = new(10);
      this.inst = inst; // Module name
      this.enabled = 0; // Module is disabled by default
   endfunction

   task setEnabled(int unsigned transCount = 1);
      enabled = 1; // Driver Enabling
      stopAfterTransCount = transCount;
      data_id = 0;
      fork
         run(); // Creating generator subprocess
      join_none; // Don't wait for ending
   endtask

   task setDisabled();
      enabled = 0; // Disable generator
   endtask

   virtual function void setCallbacks(ScoreboardGeneratorCbs cbs);
      this.cbs = cbs;
   endfunction

   task run();
      Transaction tr;
      CustomTransaction #(HDR_SIZE,MFB_ITEM_WIDTH) custom_tr;
      MvbTransaction #(MVB_ITEM_WIDTH) mvb_tr;
      MfbTransaction #(MFB_ITEM_WIDTH) mfb_tr;
      int data_len;

      while (enabled && data_id < stopAfterTransCount)
      begin
         // Copy blueprint
         tr = blueprint.copy();
         // Fill the transaction with random data
         assert(tr.randomize);
         // Cast custom transaction
         $cast(custom_tr,tr);
         if (FULL_PRINT) begin
            $write("min size: %d\n",custom_tr.dataSizeMin);
            $write("max size: %d\n",custom_tr.dataSizeMax);
         end
         // Add payload to LSB bit of HDR
         custom_tr.hdr[0] = custom_tr.payload;
         // send custom transaction to scoreboard
         cbs.post_gen(custom_tr);

         // Create MVB header packet
         mvb_tr = new();
         // add header
         mvb_tr.data[MVB_ITEM_WIDTH-1:SWITCH_WIDTH+1] = custom_tr.hdr;
         // Add switch
         mvb_tr.data[SWITCH_WIDTH:1] = custom_tr.switch;
         // Add payload
         mvb_tr.data[0] = custom_tr.payload;
         // send mvb transaction to driver
         mvbTransMbx.put(mvb_tr);

         // create MFB data packet
         if (custom_tr.payload) begin
            mfb_tr = new();
            mfb_tr.data = new[custom_tr.data.size()];
            for (int i=0; i < custom_tr.data.size(); i++) begin
               mfb_tr.data[i] = custom_tr.data[i];
            end
            // send mfb transaction to driver
            mfbTransMbx.put(mfb_tr);
         end

         //$display("MFB TRANSACTION %d SENDING TO DRIVER",data_id);
         data_id = data_id + 1;
      end // while
      enabled = 0;
      //$display("GENERATOR STOP");
   endtask

endclass
