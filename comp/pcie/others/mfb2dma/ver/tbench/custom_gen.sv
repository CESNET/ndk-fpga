/*
 * custom_gen.sv: Custom generator
 * Copyright (C) 2018 CESNET
 * Author(s): Jakub Cabal <cabal@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

//import sv_common_pkg::*;
import sv_mvb_pkg::*;
import sv_mfb_pkg::*;
import sv_dma_pkg::*;
import sv_dma_bus_pack::*;
import test_pkg::*;

class CustomGenerator;
   string inst;                      // Generator Identifier
   bit enabled;                      // Generator enabled
   ScoreboardGeneratorCbs cbs;
   tTransMbx mvbTransMbx;
   tTransMbx mfbTransMbx;

   int unsigned stopAfterTransCount; // Generator will stop after specified number of transactions
   protected int data_id;            // Transaction counter

   Transaction blueprint;

   function new (string inst);
      this.mvbTransMbx = new(2);
      this.mfbTransMbx = new(2);
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
      MvbTransaction #(DMA_DOWNHDR_WIDTH) mvb_tr;
      MfbTransaction #(MFB_ITEM_WIDTH) mfb_tr;
      DMABusCompletionTransaction dma_tr;
      int data_len;

      while (enabled && data_id < stopAfterTransCount)
      begin
         // Copy blueprint
         tr = blueprint.copy();
         // Fill the transaction with random data
         assert(tr.randomize);
         // Cast custom transaction
         $cast(mfb_tr,tr);
         // Create MVB header packet
         mvb_tr = new();
         assert(mvb_tr.randomize);
         mvb_tr.data[DMA_COMPLETION_LENGTH_O+:DMA_COMPLETION_LENGTH_W] = mfb_tr.data.size();
         // Create DMA packet
         dma_tr = new();

         dma_tr.header = {<<{mvb_tr.data}};
         dma_tr.data = {<<byte{ {<<MFB_ITEM_WIDTH{mfb_tr.data}} }};
         dma_tr.parseHeader();

         mvbTransMbx.put(mvb_tr);
         mfbTransMbx.put(mfb_tr);
         // send dma transaction to scoreboard
         cbs.post_gen(dma_tr);

         //$display("MFB TRANSACTION %d SENDING TO DRIVER",data_id);
         data_id = data_id + 1;
      end // while
      enabled = 0;
      //$display("GENERATOR STOP");
   endtask

endclass
