/*!
 * \file test.sv
 * \brief Test Cases
 * \author Jakub Cabal <cabal@cesnet.cz>
 * \date 2018
 */
 /*
 * Copyright (C) 2018 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

import sv_common_pkg::*;
import sv_mvb_pkg::*;
import sv_mfb_pkg::*;
import test_pkg::*;

program TEST (
   input  logic CLK,
   output logic RESET,
   iMvbRx.tb RX_MVB,
   iMfbRx.tb RX_MFB,
   iMvbTx.tb TX_MVB[SPLITTER_OUTPUTS-1:0],
   iMfbTx.tb TX_MFB[SPLITTER_OUTPUTS-1:0],
   iMvbTx.monitor MO_MVB[SPLITTER_OUTPUTS-1:0],
   iMfbTx.monitor MO_MFB[SPLITTER_OUTPUTS-1:0]
);
   CustomTransaction #(HDR_SIZE,MFB_ITEM_WIDTH) blueprint;
   CustomTransGenerator                         generator;

   MvbDriver    #(MFB_REGIONS,MVB_ITEM_WIDTH)                                mvb_driver;
   MfbDriver    #(MFB_REGIONS,MFB_REGION_SIZE,MFB_BLOCK_SIZE,MFB_ITEM_WIDTH) mfb_driver;

   virtual iMvbTx #(MFB_REGIONS,HDR_WIDTH)                                     vTX_MVB[SPLITTER_OUTPUTS-1:0] = TX_MVB;
   virtual iMfbTx #(MFB_REGIONS,MFB_REGION_SIZE,MFB_BLOCK_SIZE,MFB_ITEM_WIDTH) vTX_MFB[SPLITTER_OUTPUTS-1:0] = TX_MFB;
   virtual iMvbTx #(MFB_REGIONS,HDR_WIDTH)                                     vMO_MVB[SPLITTER_OUTPUTS-1:0] = MO_MVB;
   virtual iMfbTx #(MFB_REGIONS,MFB_REGION_SIZE,MFB_BLOCK_SIZE,MFB_ITEM_WIDTH) vMO_MFB[SPLITTER_OUTPUTS-1:0] = MO_MFB;

   MfbResponder #(MFB_REGIONS,MFB_REGION_SIZE,MFB_BLOCK_SIZE,MFB_ITEM_WIDTH) mfb_responder[SPLITTER_OUTPUTS-1:0];
   MfbMonitor   #(MFB_REGIONS,MFB_REGION_SIZE,MFB_BLOCK_SIZE,MFB_ITEM_WIDTH) mfb_monitor[SPLITTER_OUTPUTS-1:0];

   MvbResponder #(MVB_ITEMS,HDR_WIDTH) mvb_responder[SPLITTER_OUTPUTS-1:0];
   MvbMonitor   #(MVB_ITEMS,HDR_WIDTH) mvb_monitor[SPLITTER_OUTPUTS-1:0];

   Scoreboard scoreboard;

   task createEnvironment(int dataSizeMax, int dataSizeMin);
      blueprint = new();
      generator = new("Custom Generator");
      scoreboard = new;

      blueprint.dataSizeMax = dataSizeMax;
      blueprint.dataSizeMin = dataSizeMin;
      generator.blueprint = blueprint;
      generator.setCallbacks(scoreboard.generatorCbs);

      mvb_driver = new("MVB Driver", generator.mvbTransMbx, RX_MVB);
      mfb_driver = new("MFB Driver", generator.mfbTransMbx, RX_MFB);

      mvb_driver.wordDelayEnable_wt  = MVB_GAP_CHANCE;
      mvb_driver.wordDelayDisable_wt = 100-MVB_GAP_CHANCE;
      mvb_driver.wordDelayHigh       = MVB_GAP_MAX_SIZE;

      mfb_driver.wordDelayEnable_wt  = MFB_GAP_CHANCE;
      mfb_driver.wordDelayDisable_wt = 100-MFB_GAP_CHANCE;
      mfb_driver.wordDelayHigh       = MFB_GAP_MAX_SIZE;

      for (int i = 0; i < SPLITTER_OUTPUTS; i++) begin
         mvb_responder[i] = new($sformatf("MVB Responder %03d",i), vTX_MVB[i]);
         mfb_responder[i] = new($sformatf("MFB Responder %03d",i), vTX_MFB[i]);

         mvb_monitor[i] = new($sformatf("MVB Monitor %03d",i), vMO_MVB[i]);
         mfb_monitor[i] = new($sformatf("MFB Monitor %03d",i), vMO_MFB[i]);

         mvb_monitor[i].setCallbacks(scoreboard.mvbMonitorCbs[i]);
         mfb_monitor[i].setCallbacks(scoreboard.mfbMonitorCbs[i]);
      end

      mvb_responder[0].wordDelayEnable_wt  = MVB0_RES_GAP_CHANCE;
      mvb_responder[0].wordDelayDisable_wt = 100-MVB1_RES_GAP_CHANCE;
      mvb_responder[0].wordDelayHigh       = MVB0_RES_GAP_MAX_SIZE;
      mvb_responder[1].wordDelayEnable_wt  = MVB1_RES_GAP_CHANCE;
      mvb_responder[1].wordDelayDisable_wt = 100-MVB1_RES_GAP_CHANCE;
      mvb_responder[1].wordDelayHigh       = MVB1_RES_GAP_MAX_SIZE;

      mfb_responder[0].wordDelayEnable_wt  = MFB0_RES_GAP_CHANCE;
      mfb_responder[0].wordDelayDisable_wt = 100-MFB1_RES_GAP_CHANCE;
      mfb_responder[0].wordDelayHigh       = MFB0_RES_GAP_MAX_SIZE;
      mfb_responder[1].wordDelayEnable_wt  = MFB1_RES_GAP_CHANCE;
      mfb_responder[1].wordDelayDisable_wt = 100-MFB1_RES_GAP_CHANCE;
      mfb_responder[1].wordDelayHigh       = MFB1_RES_GAP_MAX_SIZE;
   endtask

   task resetDesign();
      RESET=1;
      #RESET_TIME RESET = 0;
   endtask

   task enableTestEnvironment();
      scoreboard.setEnabled();
      mvb_driver.setEnabled();
      mfb_driver.setEnabled();
      for (int i = 0; i < SPLITTER_OUTPUTS; i++) begin
         mvb_monitor[i].setEnabled();
         mvb_responder[i].setEnabled();
         mfb_monitor[i].setEnabled();
         mfb_responder[i].setEnabled();
      end
   endtask

   task disableTestEnvironment();
      automatic int busy = 1;

      wait(!mfb_driver.busy && !mvb_driver.busy);
      do begin
         wait(!mfb_monitor[0].busy);
         fork : StayIdleWait0
            wait(mfb_monitor[0].busy) disable StayIdleWait0;
            #(100*CLK_PERIOD) disable StayIdleWait0;
         join
         busy = 0;
         for (int i = 0; i < SPLITTER_OUTPUTS; i++)
            busy |= mvb_monitor[i].busy || mfb_monitor[i].busy;
      end while(mfb_driver.busy || mvb_driver.busy || busy);
      mvb_driver.setDisabled();
      mfb_driver.setDisabled();
      for (int i = 0; i < SPLITTER_OUTPUTS; i++) begin
         mvb_monitor[i].setDisabled();
         mvb_responder[i].setDisabled();
         mfb_monitor[i].setDisabled();
         mfb_responder[i].setDisabled();
      end
      scoreboard.setDisabled();
   endtask

   task test1();
      $write("\n\n############ TEST CASE 1 ############\n\n");
      enableTestEnvironment();
      generator.setEnabled(TRANSACTION_COUNT);
      wait(!generator.enabled);
      disableTestEnvironment();
      scoreboard.display();
   endtask

   initial begin
      resetDesign();
      createEnvironment(FRAME_SIZE_MAX, FRAME_SIZE_MIN);
      test1();
      $write("Verification finished successfully!\n");
      $stop();
   end

endprogram
