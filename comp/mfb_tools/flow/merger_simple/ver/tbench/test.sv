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
    iMfbRx.tb RX0,
    iMfbRx.tb RX1,
    iMfbTx.tb TX,
    iMfbTx.monitor MONITOR
);

    MfbTransaction #(ITEM_WIDTH) blueprint;
    Generator generator0;
    Generator generator1;
    MfbDriver #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) driver0;
    MfbDriver #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) driver1;
    MfbResponder #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) responder;
    MfbMonitor #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) monitor;
    Scoreboard scoreboard;

    task createGeneratorEnvironment(int packet_size_max, int packet_size_min);
        generator0 = new("Generator0", 0);
        generator1 = new("Generator1", 0);
        blueprint = new;
        blueprint.frameSizeMax = packet_size_max;
        blueprint.frameSizeMin = packet_size_min;
        generator0.blueprint = blueprint;
        generator1.blueprint = blueprint;
    endtask

    task createEnvironment();
        driver0  = new("Driver0", generator0.transMbx, RX0);
        driver1  = new("Driver1", generator1.transMbx, RX1);
        monitor = new("Monitor", MONITOR);
        responder = new("Responder", TX);
        scoreboard = new;
        driver0.setCallbacks(scoreboard.driverCbs);
        driver1.setCallbacks(scoreboard.driverCbs);
        monitor.setCallbacks(scoreboard.monitorCbs);
    endtask

    task resetDesign();
        RESET=1;
        #RESET_TIME RESET = 0;
    endtask

    task enableTestEnvironment();
        driver0.setEnabled();
        driver1.setEnabled();
        responder.setEnabled();
    endtask

    task disableTestEnvironment();
        wait(!driver0.busy && !driver1.busy);
        do begin
            wait(!monitor.busy);
            fork : StayIdleWait0
                wait(monitor.busy) disable StayIdleWait0;
                #(100*CLK_PERIOD) disable StayIdleWait0;
            join
        end while(monitor.busy);
        driver0.setDisabled();
        driver1.setDisabled();
        monitor.setDisabled();
        responder.setDisabled();
    endtask

    task test1();
        $write("\n\n############ TEST CASE 1 ############\n\n");
        monitor.setEnabled();
        generator0.setEnabled((3*TRANSACTION_COUNT)/10);
        generator1.setEnabled((7*TRANSACTION_COUNT)/10);
        wait(!generator0.enabled && !generator1.enabled);
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
