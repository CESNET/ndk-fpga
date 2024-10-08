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
   iMfbTx.tb TX_MFB,
   iMfbTx.monitor MONITOR
);
   MvbTransaction #(LEN_WIDTH)                               blueprint;
   Generator                                                 generator;
   MvbDriver    #(REGIONS,LEN_WIDTH)                         mvb_driver;
   MfbResponder #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) mfb_responder;
   MfbMonitor   #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) mfb_monitor;
   Scoreboard                                                scoreboard;

   task createEnvironment();
      generator     = new("Generator", 0);
      mvb_driver    = new("MVB Driver", generator.transMbx, RX_MVB);
      mfb_monitor   = new("MFB Monitor", MONITOR);
      mfb_responder = new("MFB Responder", TX_MFB);
      scoreboard    = new();
      blueprint     = new();

      //mvb_driver.wordDelayEnable_wt = 20;
      //mvb_driver.wordDelayDisable_wt = 1;
      //mvb_driver.wordDelayLow = 10;
      //mvb_driver.wordDelayHigh = 20;
      //mfb_responder.wordDelayEnable_wt = 0;
      //mfb_responder.wordDelayDisable_wt = 1;

      generator.blueprint = blueprint;
      mvb_driver.setCallbacks(scoreboard.driverCbs);
      mfb_monitor.setCallbacks(scoreboard.monitorCbs);
   endtask

   task resetDesign();
      RESET=1;
      #RESET_TIME RESET = 0;
   endtask

   task enableTestEnvironment();
      mvb_driver.setEnabled();
      mfb_monitor.setEnabled();
      mfb_responder.setEnabled();
   endtask

   task disableTestEnvironment();
      wait(!mvb_driver.busy);
      do begin
         wait(!mfb_monitor.busy);
         fork : StayIdleWait0
            wait(mfb_monitor.busy) disable StayIdleWait0;
            #(100*CLK_PERIOD) disable StayIdleWait0;
         join
      end while(mfb_monitor.busy);
      mvb_driver.setDisabled();
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
      createEnvironment();
      test1();
      $write("Verification finished successfully!\n");
      $stop();
   end

endprogram
