/*!
 * \file test.sv
 * \brief Test Cases
 * \author Jakub Cabal <xcabal05@stud.feec.vutbr.cz>
 * \date 2017
 */
 /*
 * Copyright (C) 2017 CESNET z. s. p. o.
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
    iMfbRx.tb RX,
    iMfbTx.tb TX0,
    iMfbTx.tb TX1,
    iMfbTx.monitor MONITOR0,
    iMfbTx.monitor MONITOR1
);


    MfbTransaction #(ITEM_WIDTH) blueprint;
    Generator generator;
    MfbDriver #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) driver;
    MfbResponder #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) responder0;
    MfbMonitor #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) monitor0;
    MfbResponder #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) responder1;
    MfbMonitor #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) monitor1;
    Scoreboard scoreboard;


    task createGeneratorEnvironment(int packet_size_max, int packet_size_min);
        generator = new("Generator", 0);
        blueprint = new;
        blueprint.frameSizeMax = packet_size_max;
        blueprint.frameSizeMin = packet_size_min;
        generator.blueprint = blueprint;
    endtask

    task createEnvironment();
        driver  = new("Driver", generator.transMbx, RX);
        monitor0 = new("Monitor", MONITOR0);
        responder0 = new("Responder", TX0);
        monitor1 = new("Monitor", MONITOR1);
        responder1 = new("Responder", TX1);
        scoreboard = new;
        driver.setCallbacks(scoreboard.driverCbs);
        monitor0.setCallbacks(scoreboard.monitorCbs0);
        monitor1.setCallbacks(scoreboard.monitorCbs1);
    endtask

    task resetDesign();
        RESET=1;
        #RESET_TIME RESET = 0;
    endtask

    task enableTestEnvironment();
        driver.setEnabled();
        monitor0.setEnabled();
        responder0.setEnabled();
        monitor1.setEnabled();
        responder1.setEnabled();
    endtask

    task disableTestEnvironment();
        wait(!driver.busy);
        do begin
            wait(!monitor0.busy);
            fork : StayIdleWait0
                wait(monitor0.busy) disable StayIdleWait0;
                #(100*CLK_PERIOD) disable StayIdleWait0;
            join
        end while(monitor0.busy);
        do begin
            wait(!monitor1.busy);
            fork : StayIdleWait1
                wait(monitor1.busy) disable StayIdleWait1;
                #(100*CLK_PERIOD) disable StayIdleWait1;
            join
        end while(monitor1.busy);
        driver.setDisabled();
        monitor0.setDisabled();
        responder0.setDisabled();
        monitor1.setDisabled();
        responder1.setDisabled();
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
