/*!
 * \file test.sv
 * \brief Test Cases
 * \author Jakub Cabal <cabal@cesnet.cz>
 * \date 2018
 */
 /*
 * Copyright (C) 2018 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

import sv_common_pkg::*;
import sv_mvb_pkg::*;
import sv_mfb_pkg::*;
import sv_dma_pkg::*;
import test_pkg::*;

program TEST (
   input  logic CLK,
   output logic RESET,
   iMvbRx.tb RX_MVB,
   iMfbRx.tb RX_MFB,
   iDMABusTx.tb TX_DMA,
   iDMABusTx.monitor MO_DMA
);
   MfbTransaction #(MFB_ITEM_WIDTH) blueprint;
   CustomGenerator                  generator;

   MvbDriver    #(MVB_ITEMS,DMA_DOWNHDR_WIDTH)                               mvb_driver;
   MfbDriver    #(MFB_REGIONS,MFB_REGION_SIZE,MFB_BLOCK_SIZE,MFB_ITEM_WIDTH) mfb_driver;

   DMABusResponder #(MFB_REGIONS*MFB_REG_WIDTH, DMA_DOWNHDR_WIDTH) dma_responder;
   DMABusMonitor   #(MFB_REGIONS*MFB_REG_WIDTH, DMA_DOWNHDR_WIDTH, DMABusCompletionTransaction) dma_monitor;

   Scoreboard scoreboard;

   task createEnvironment(int dataSizeMax, int dataSizeMin);
      blueprint = new();
      generator = new("Custom Generator");
      scoreboard = new;

      blueprint.frameSizeMax = dataSizeMax;
      blueprint.frameSizeMin = dataSizeMin;
      generator.blueprint = blueprint;
      generator.setCallbacks(scoreboard.generatorCbs);

      mvb_driver = new("MVB Driver", generator.mvbTransMbx, RX_MVB);
      mfb_driver = new("MFB Driver", generator.mfbTransMbx, RX_MFB);
      mvb_driver.setCallbacks(scoreboard.driverCbs);
      mfb_driver.setCallbacks(scoreboard.driverCbs);

      dma_responder = new("Responder DMA", TX_DMA);
      dma_monitor = new("Monitor DMA", MO_DMA);

      dma_monitor.setCallbacks(scoreboard.monitorCbs);
   endtask

   task resetDesign();
      RESET=1;
      #RESET_TIME RESET = 0;
   endtask

   task enableTestEnvironment();
      mvb_driver.setEnabled();
      mfb_driver.setEnabled();
      dma_monitor.setEnabled();
      dma_responder.setEnabled();
   endtask

   task disableTestEnvironment();
      wait(!mfb_driver.busy && !mvb_driver.busy);
      do begin
         wait(!dma_monitor.busy);
         fork : StayIdleWait0
            wait(dma_monitor.busy) disable StayIdleWait0;
            #(100*CLK_PERIOD) disable StayIdleWait0;
         join
      end while(dma_monitor.busy);
      mvb_driver.setDisabled();
      mfb_driver.setDisabled();
      dma_monitor.setDisabled();
      dma_responder.setDisabled();
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
