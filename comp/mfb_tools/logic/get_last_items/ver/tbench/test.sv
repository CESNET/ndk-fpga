/*!
 * \file test.sv
 * \brief Test Cases
 * \author Jakub Cabal <cabal@cesnet.cz>
 * \date 2026
 */
 /*
 * Copyright (C) 2026 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

import sv_common_pkg::*;
import sv_mfb_pkg::*;
import sv_mvb_pkg::*;
import test_pkg::*;

program TEST (
   input logic CLK,
   output logic RESET,
   iMfbRx.tb      RX,
   iMfbTx.tb      TX,
   iMfbTx.monitor TX_MONITOR,
   iMvbTx.tb      EX,
   iMvbTx.monitor EX_MONITOR
);

   MfbTransaction #(ITEM_WIDTH) blueprint;
   Generator    generator;
   MfbDriver    #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) mfb_driver;
   MfbResponder #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) mfb_responder;
   MfbMonitor   #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) mfb_monitor;
   MvbResponder #(REGIONS,EXTRACTED_ITEMS*ITEM_WIDTH) mvb_responder;
   MvbMonitor   #(REGIONS,EXTRACTED_ITEMS*ITEM_WIDTH) mvb_monitor;
   Scoreboard   scoreboard;

   task automatic createGeneratorEnvironment(int packet_size_max, int packet_size_min);
      generator = new("Generator", 0);
      blueprint = new;
      blueprint.frameSizeMax = packet_size_max;
      blueprint.frameSizeMin = packet_size_min;
      generator.blueprint = blueprint;
   endtask

   task automatic createEnvironment();
      mfb_driver    = new("MFB Driver", generator.transMbx, RX);
      mfb_monitor   = new("MFB Monitor", TX_MONITOR);
      mfb_responder = new("MFB Responder", TX);
      mvb_monitor   = new("MVB Monitor", EX_MONITOR);
      mvb_responder = new("MVB Responder", EX);
      mvb_responder.wordDelayEnable_wt = 1;
      mvb_responder.wordDelayDisable_wt = 10;

      scoreboard = new;
      mfb_driver.setCallbacks(scoreboard.driverCbs);
      mvb_monitor.setCallbacks(scoreboard.monitorCbs);
   endtask

   task automatic resetDesign();
      RESET=1;
      #RESET_TIME RESET = 0;
   endtask

   task automatic enableTestEnvironment();
      mfb_driver.setEnabled();
      mfb_monitor.setEnabled();
      mfb_responder.setEnabled();
      mvb_monitor.setEnabled();
      mvb_responder.setEnabled();
   endtask

   task automatic disableTestEnvironment();
      wait(!mfb_driver.busy);
      do begin
         wait(!mvb_monitor.busy);
         fork : StayIdleWait
            wait(mvb_monitor.busy) disable StayIdleWait;
            #(100*CLK_PERIOD) disable StayIdleWait;
         join
      end while(mvb_monitor.busy);
      mfb_driver.setDisabled();
      mfb_monitor.setDisabled();
      mfb_responder.setDisabled();
   endtask

   task automatic test1();
      $write("\n\n############ TEST CASE 1 ############\n\n");
      enableTestEnvironment();
      resetDesign();
      generator.setEnabled(TRANSACTION_COUNT);
      wait(!generator.enabled);
      disableTestEnvironment();
      scoreboard.display();
   endtask

   initial begin
      createGeneratorEnvironment(FRAME_SIZE_MAX, FRAME_SIZE_MIN);
      createEnvironment();
      test1();
      if (scoreboard.done()) begin
        $write("Verification finished successfully!\n");
      end
      $stop();
   end

endprogram
