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
import sv_mvb_pkg::*;
import test_pkg::*;

program TEST (
   input logic RX_CLK,
   input logic TX_CLK,
   output logic RESET,
   iMvbRx.tb      FD_RX,
   iMvbTx.tb      FD_TX,
   iMvbTx.monitor FD_TX_MONITOR,
   iMfbRx.tb      RX,
   iMfbTx.tb      TX,
   iMfbTx.monitor TX_MONITOR
);

   MfbTransaction #(ITEM_WIDTH,1) blueprint;
   Generator    generator;
   MfbDriver    #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH,0,1,1) mfb_driver;
   MfbResponder #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) mfb_responder;
   MfbMonitor   #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) mfb_monitor;

   MvbTransaction #(1)       fd_blueprint;
   Generator                 fd_generator;
   MvbDriver    #(1,1)       fd_driver;
   MvbResponder #(REGIONS,1) fd_responder;
   MvbMonitor   #(REGIONS,1) fd_monitor;

   Scoreboard   scoreboard;

   task createGeneratorEnvironment(int packet_size_max, int packet_size_min);
      generator = new("Generator", 0);
      blueprint = new;
      blueprint.frameSizeMax = packet_size_max;
      blueprint.frameSizeMin = packet_size_min;
      generator.blueprint = blueprint;

      fd_generator = new("FD Generator", 0);
      fd_blueprint = new;
      fd_generator.blueprint = fd_blueprint;

   endtask

   task createEnvironment();
      mfb_driver    = new("MFB Driver", generator.transMbx, RX);
      mfb_monitor   = new("MFB Monitor", TX_MONITOR);
      mfb_responder = new("MFB Responder", TX);
      mfb_responder.wordDelayEnable_wt  = DST_RDY_DOWN_CHANCE;
      mfb_responder.wordDelayDisable_wt = 100-DST_RDY_DOWN_CHANCE;
      mfb_responder.wordDelayLow        = DST_RDY_DOWN_TIME_MIN;
      mfb_responder.wordDelayHigh       = DST_RDY_DOWN_TIME_MAX;

      fd_driver  = new("FD Driver", fd_generator.transMbx, FD_RX);
      fd_driver.wordDelayEnable_wt  = FD_SRC_RDY_DOWN_CHANCE;
      fd_driver.wordDelayDisable_wt = 100-FD_SRC_RDY_DOWN_CHANCE;
      fd_driver.wordDelayLow        = FD_SRC_RDY_DOWN_TIME_MIN;
      fd_driver.wordDelayHigh       = FD_SRC_RDY_DOWN_TIME_MAX;
      fd_monitor = new("FD Monitor", FD_TX_MONITOR);
      fd_responder = new("FD Responder", FD_TX);
      fd_responder.wordDelayEnable_wt = 0;
      fd_responder.wordDelayDisable_wt = 1;

      scoreboard    = new;

      mfb_driver.setCallbacks(scoreboard.driverCbs);
      mfb_monitor.setCallbacks(scoreboard.monitorCbs);
      fd_monitor.setCallbacks(scoreboard.fd_monitorCbs);
   endtask

   task resetDesign();
      RESET=1;
      #RESET_TIME RESET = 0;
   endtask

   task enableTestEnvironment();
      mfb_driver.setEnabled();
      mfb_responder.setEnabled();
      fd_driver.setEnabled();
      fd_responder.setEnabled();
      scoreboard.setEnabled();
   endtask

   task disableTestEnvironment();
      wait(!mfb_driver.busy);
      do begin
         wait(!mfb_monitor.busy);
         fork : StayIdleWait
            wait(mfb_monitor.busy) disable StayIdleWait;
            #(100*TX_CLK_PERIOD) disable StayIdleWait;
         join
      end while(mfb_monitor.busy);
      mfb_driver.setDisabled();
      mfb_monitor.setDisabled();
      mfb_responder.setDisabled();
      fd_driver.setDisabled();
      fd_monitor.setDisabled();
      fd_responder.setDisabled();
      scoreboard.setDisabled();
   endtask

   task test1();
      $write("\n\n############ TEST CASE 1 ############\n\n");
      mfb_monitor.setEnabled();
      fd_monitor.setEnabled();
      fd_generator.setEnabled(TRANSACTION_COUNT);
      generator.setEnabled(TRANSACTION_COUNT);
      wait(!generator.enabled);
      disableTestEnvironment();
      scoreboard.display();
   endtask

   initial begin
      createGeneratorEnvironment(FRAME_SIZE_MAX, FRAME_SIZE_MIN);
      createEnvironment();
      enableTestEnvironment();
      resetDesign();
      test1();
      $write("Verification finished successfully!\n");
      $stop();
   end

endprogram
