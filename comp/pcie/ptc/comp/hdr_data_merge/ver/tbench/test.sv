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
   input  logic DMA_CLK,
   output logic DMA_RESET,
   input  logic PCIE_CLK,
   output logic PCIE_RESET,
   iMvbRx.tb RX_MVB,
   iMfbRx.tb RX_MFB,
   iMfbTx.tb TX_MFB,
   iMfbTx.monitor MONITOR
);
   CustomTransaction #(HDR_WIDTH,MFB_ITEM_WIDTH)                             blueprint;
   CustomTransGenerator                                                      generator;
   MvbDriver    #(MVB_ITEMS,MVB_ITEM_WIDTH)                                  mvb_driver;
   MfbDriver    #(MFB_REGIONS,MFB_REGION_SIZE,MFB_BLOCK_SIZE,MFB_ITEM_WIDTH) mfb_driver;
   MfbResponder #(MFB_REGIONS,MFB_REGION_SIZE,MFB_BLOCK_SIZE,MFB_ITEM_WIDTH) mfb_responder;
   MfbMonitor   #(MFB_REGIONS,MFB_REGION_SIZE,MFB_BLOCK_SIZE,MFB_ITEM_WIDTH) mfb_monitor;
   Scoreboard scoreboard;

   task createEnvironment(int payloadRate, int payloadSizeMax, int payloadSizeMin);
      generator     = new("Custom Generator");
      mvb_driver    = new("MVB Driver", generator.mvbTransMbx, RX_MVB);
      mfb_driver    = new("MFB Driver", generator.mfbTransMbx, RX_MFB);
      mfb_driver.mode           = mfb_driver.MODE_RANDOM;
      mfb_driver.ifgHigh        = 100;
      mfb_driver.wordDelayHigh  = 0;
      mfb_monitor   = new("MFB Monitor", MONITOR);
      mfb_responder = new("MFB Responder", TX_MFB);
      scoreboard    = new;

      blueprint = new();
      blueprint.payloadRate = payloadRate;
      blueprint.payloadSizeMax = payloadSizeMax;
      blueprint.payloadSizeMin = payloadSizeMin;

      //mfb_responder.wordDelayEnable_wt = 0;
      //mfb_responder.wordDelayDisable_wt = 1;

      generator.blueprint = blueprint;
      generator.setCallbacks(scoreboard.generatorCbs);
      mfb_monitor.setCallbacks(scoreboard.monitorCbs);
   endtask

   task resetDesign();
      DMA_RESET=1;
      PCIE_RESET=1;
      #DMA_RESET_TIME DMA_RESET = 0;
      #PCIE_RESET_TIME PCIE_RESET = 0;
   endtask

   task enableTestEnvironment();
      mvb_driver.setEnabled();
      mfb_driver.setEnabled();
      mfb_responder.setEnabled();
   endtask

   task disableTestEnvironment();
      wait(!mfb_driver.busy && !mvb_driver.busy);
      do begin
         wait(!mfb_monitor.busy);
         fork : StayIdleWait0
            wait(mfb_monitor.busy) disable StayIdleWait0;
            #(100*PCIE_CLK_PERIOD) disable StayIdleWait0;
         join
      end while(mfb_monitor.busy);
      mvb_driver.setDisabled();
      mfb_driver.setDisabled();
      mfb_monitor.setDisabled();
      mfb_responder.setDisabled();
   endtask

   task test1();
      $write("\n\n############ TEST CASE 1 ############\n\n");
      mfb_monitor.setEnabled();
      generator.setEnabled(TRANSACTION_COUNT);
      wait(!generator.enabled);
      disableTestEnvironment();
      scoreboard.display();
   endtask

   initial begin
      createEnvironment(PAYLOAD_RATE, PAYLOAD_SIZE_MAX, PAYLOAD_SIZE_MIN);
      enableTestEnvironment();
      resetDesign();
      test1();
      $write("Verification finished successfully!\n");
      $stop();
   end

endprogram
