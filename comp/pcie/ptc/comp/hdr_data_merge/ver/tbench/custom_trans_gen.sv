/*
 * custom_trans_gen.sv: Custom transaction generator
 * Copyright (C) 2018 CESNET z. s. p. o.
 * Author(s): Jakub Cabal <cabal@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
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
      this.mvbTransMbx = new(25);
      this.mfbTransMbx = new(25);
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
      CustomTransaction #(HDR_WIDTH,MFB_ITEM_WIDTH) custom_tr;
      MvbTransaction #(MVB_ITEM_WIDTH) mvb_tr;
      MfbTransaction #(MFB_ITEM_WIDTH) mfb_tr;
      int payload_len;

      while (enabled && data_id < stopAfterTransCount)
      begin
         // Copy blueprint
         tr = blueprint.copy();
         // Fill the transaction with random data
         assert(tr.randomize);

         $cast(custom_tr,tr);
         payload_len = custom_tr.payload.size();

         // Set correct lenght to header of custom transaction
         if (custom_tr.payload_en == 1) begin
            custom_tr.header[74:64] = payload_len;
         end else begin
            custom_tr.header[74:64] = 0;
         end

         // Create MVB header packet
         mvb_tr = new();
         // add header data
         mvb_tr.data[MVB_ITEM_WIDTH-1:1] = custom_tr.header;
         // Add payload flag
         if (custom_tr.payload_en == 1) begin
            mvb_tr.data[0] = 1'b1;
         end else begin
            mvb_tr.data[0] = 1'b0;
         end

         // create MFB data packet
         if (custom_tr.payload_en == 1) begin
            mfb_tr = new();
            mfb_tr.data = new[payload_len];
            for (int i=0; i < payload_len; i++) begin
               mfb_tr.data[i] = custom_tr.payload[i];
            end
         end

         cbs.post_gen(custom_tr); // call back to scoreboard
         mvbTransMbx.put(mvb_tr);
         if (custom_tr.payload_en == 1) begin
            mfbTransMbx.put(mfb_tr);
         end
         //$display("MFB TRANSACTION %d SENDING TO DRIVER",data_id);
         data_id = data_id + 1;
      end // while
      enabled = 0;
      //$display("GENERATOR STOP");
   endtask

endclass
