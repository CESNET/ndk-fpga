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
import sv_mfb_pkg::*;
import test_pkg::*;

program TEST (
   input logic CLK,
   output logic RESET,
   iMfbRx.tb      RX,
   iMfbTx.tb      TX,
   iMfbTx.monitor TX_MONITOR
);

   MfbTransaction #(ITEM_WIDTH,1) blueprint;
   Generator    generator;
   MfbDriver    #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH,0,1) mfb_driver;
   MfbResponder #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) mfb_responder;
   MfbMonitor   #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) mfb_monitor;
   Scoreboard   scoreboard;

   task createGeneratorEnvironment(int packet_size_max, int packet_size_min);
      generator = new("Generator", 0);
      blueprint = new;
      blueprint.frameSizeMax = packet_size_max;
      blueprint.frameSizeMin = packet_size_min;
      generator.blueprint = blueprint;
   endtask

   task createEnvironment();
      mfb_driver    = new("MFB Driver", generator.transMbx, RX);
      mfb_monitor   = new("MFB Monitor", TX_MONITOR);
      mfb_responder = new("MFB Responder", TX);
      scoreboard    = new;

      mfb_driver.setCallbacks(scoreboard.driverCbs);
      mfb_monitor.setCallbacks(scoreboard.monitorCbs);
   endtask

   task resetDesign();
      RESET=1;
      #RESET_TIME RESET = 0;
   endtask

   task enableTestEnvironment();
      mfb_driver.setEnabled();
      mfb_monitor.setEnabled();
      mfb_responder.setEnabled();
   endtask

   task disableTestEnvironment();
      wait(!mfb_driver.busy);
      do begin
         wait(!mfb_monitor.busy);
         fork : StayIdleWait
            wait(mfb_monitor.busy) disable StayIdleWait;
            #(100*CLK_PERIOD) disable StayIdleWait;
         join
      end while(mfb_monitor.busy);
      mfb_driver.setDisabled();
      mfb_monitor.setDisabled();
      mfb_responder.setDisabled();
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
      createGeneratorEnvironment(FRAME_SIZE_MAX, FRAME_SIZE_MIN);
      createEnvironment();
      test1();
      $write("Verification finished successfully!\n");
      $stop();
   end

endprogram
