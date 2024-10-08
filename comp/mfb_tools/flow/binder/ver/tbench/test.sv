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
   iMfbRx.tb RX0,
   iMfbRx.tb RX1,
   iMfbRx.tb RX2,
   iMfbRx.tb RX3,
   iMfbTx.tb TX,
   iMfbTx.monitor MONITOR
);


   MfbTransaction #(ITEM_WIDTH) blueprint0;
   MfbTransaction #(ITEM_WIDTH) blueprint1;
   MfbTransaction #(ITEM_WIDTH) blueprint2;
   MfbTransaction #(ITEM_WIDTH) blueprint3;
   Generator generator0;
   Generator generator1;
   Generator generator2;
   Generator generator3;
   MfbDriver #(1,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) driver0;
   MfbDriver #(1,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) driver1;
   MfbDriver #(1,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) driver2;
   MfbDriver #(1,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) driver3;

   MfbResponder #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) responder;
   MfbMonitor #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) monitor;
   Scoreboard scoreboard;

    task createGeneratorEnvironment(int packet_size_max, int packet_size_min);
      generator0 = new("Generator0", 0);
      blueprint0 = new;
      blueprint0.frameSizeMax = packet_size_max;
      blueprint0.frameSizeMin = packet_size_min;
      generator0.blueprint = blueprint0;

      generator1 = new("Generator1", 0);
      blueprint1 = new;
      blueprint1.frameSizeMax = packet_size_max;
      blueprint1.frameSizeMin = packet_size_min;
      generator1.blueprint = blueprint1;

      generator2 = new("Generator2", 0);
      blueprint2 = new;
      blueprint2.frameSizeMax = packet_size_max;
      blueprint2.frameSizeMin = packet_size_min;
      generator2.blueprint = blueprint2;

      generator3 = new("Generator3", 0);
      blueprint3 = new;
      blueprint3.frameSizeMax = packet_size_max;
      blueprint3.frameSizeMin = packet_size_min;
      generator3.blueprint = blueprint3;
    endtask

    task createEnvironment();
        driver0 = new("Driver0", generator0.transMbx, RX0);
        driver1 = new("Driver1", generator1.transMbx, RX1);
        driver2 = new("Driver2", generator2.transMbx, RX2);
        driver3 = new("Driver3", generator3.transMbx, RX3);
        monitor = new("Monitor", MONITOR);
        responder = new("Responder", TX);
        scoreboard = new;

        //responder.wordDelayEnable_wt = 0;
        //responder.wordDelayDisable_wt = 1;
        //driver0.ifgEnable_wt = 0;
        //driver0.ifgDisable_wt = 1;
        //driver1.ifgEnable_wt = 0;
        //driver1.ifgDisable_wt = 1;
        //driver2.ifgEnable_wt = 0;
        //driver2.ifgDisable_wt = 1;
        //driver3.ifgEnable_wt = 0;
        //driver3.ifgDisable_wt = 1;

        driver0.setCallbacks(scoreboard.driverCbs);
        driver1.setCallbacks(scoreboard.driverCbs);
        driver2.setCallbacks(scoreboard.driverCbs);
        driver3.setCallbacks(scoreboard.driverCbs);
        monitor.setCallbacks(scoreboard.monitorCbs);
    endtask

    task resetDesign();
        RESET=1;
        #RESET_TIME RESET = 0;
    endtask

    task enableTestEnvironment();
      driver0.setEnabled();
      driver1.setEnabled();
      driver2.setEnabled();
      driver3.setEnabled();
      monitor.setEnabled();
      responder.setEnabled();
    endtask

    task disableTestEnvironment();
        wait(!driver0.busy && !driver1.busy && !driver2.busy && !driver3.busy);
        do begin
            wait(!monitor.busy);
            fork : StayIdleWait
                wait(monitor.busy) disable StayIdleWait;
                #(100*CLK_PERIOD) disable StayIdleWait;
            join
        end while(monitor.busy);
        driver0.setDisabled();
        driver1.setDisabled();
        driver2.setDisabled();
        driver3.setDisabled();
        monitor.setDisabled();
        responder.setDisabled();
    endtask


    task test1();
        $write("\n\n############ TEST CASE 1 ############\n\n");
        enableTestEnvironment();
        generator0.setEnabled(TRANSACTION_COUNT);
        generator1.setEnabled(TRANSACTION_COUNT);
        generator2.setEnabled(TRANSACTION_COUNT);
        generator3.setEnabled(TRANSACTION_COUNT);
        wait(!generator0.enabled && !generator1.enabled && !generator2.enabled && !generator3.enabled);
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
