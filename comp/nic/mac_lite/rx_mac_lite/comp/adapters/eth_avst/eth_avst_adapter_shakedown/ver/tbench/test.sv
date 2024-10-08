// file test.sv: Test Cases
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kondys <xkondy00@vutbr.cz>
//
// SPDX-License-Identifier: BSD-3-Clause


import sv_common_pkg::*;
import sv_mfb_pkg::*;
import test_pkg::*;

program TEST (
    input logic CLK,
    output logic RESET,
    iMfbRx.tb RX,
    iMfbTx.tb TX,
    iMfbTx.monitor MONITOR
);

    MfbTransaction blueprint;
    Generator generator;
    MfbDriver    #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH,0,1,1) driver;
    MfbResponder #(TX_REGIONS,TX_REGION_SIZE,TX_BLOCK_SIZE,TX_ITEM_WIDTH) responder;
    MfbMonitor   #(TX_REGIONS,TX_REGION_SIZE,TX_BLOCK_SIZE,TX_ITEM_WIDTH) monitor;
    Scoreboard scoreboard;


    task createGeneratorEnvironment(int packet_size_max, int packet_size_min);
        generator = new("Generator", 0);
        blueprint = new;
        blueprint.frameSizeMax = packet_size_max;
        blueprint.frameSizeMin = packet_size_min;
        generator.blueprint = blueprint;
    endtask

    task createEnvironment();
        driver     = new("Driver", generator.transMbx, RX);
        monitor    = new("Monitor", MONITOR);
        responder  = new("Responder", TX);
        scoreboard = new;
        driver.setCallbacks(scoreboard.driverCbs);
        //driver.wordDelayEnable_wt = 0;
        //driver.wordDelayDisable_wt = 1;
        monitor.setCallbacks(scoreboard.monitorCbs);
        responder.wordDelayEnable_wt = 0;
        responder.wordDelayDisable_wt = 1;
    endtask

    task resetDesign();
        RESET=1;
        #RESET_TIME RESET = 0;
    endtask

    task enableTestEnvironment();
        driver.setEnabled();
        monitor.setEnabled();
        responder.setEnabled();
    endtask

    task disableTestEnvironment();
        wait(!driver.busy);
        do begin
            wait(!monitor.busy);
            fork : StayIdleWait0
                wait(monitor.busy) disable StayIdleWait0;
                #(100*CLK_PERIOD) disable StayIdleWait0;
            join
        end while(monitor.busy);
        driver.setDisabled();
        monitor.setDisabled();
        responder.setDisabled();
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
