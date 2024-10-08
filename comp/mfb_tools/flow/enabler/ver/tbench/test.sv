/*!
 * \file test.sv
 * \brief Test Cases
 * \author Jakub Cabal <cabal@cesnet.cz>
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
import sv_mvb_pkg::*;
import test_pkg::*;

program TEST (
    input logic CLK,
    output logic RESET,
    iMvbRx.tb REG,
    iMfbRx.tb RX,
    iMfbTx.tb TX,
    iMfbTx.monitor MONITOR
);

    MvbTransaction #(8) reg_blueprint;
    Generator           reg_generator;
    MvbDriver #(1,8)    reg_driver;

    MfbTransaction #(ITEM_WIDTH) blueprint;
    Generator                    generator;
    MfbDriver    #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) driver;
    MfbResponder #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) responder;
    MfbMonitor   #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) monitor;

    Scoreboard scoreboard;

    task createGeneratorEnvironment(int packet_size_max, int packet_size_min);
        reg_generator = new("REG Generator", 0);
        reg_blueprint = new;
        reg_generator.blueprint = reg_blueprint;

        generator = new("Generator", 0);
        blueprint = new;
        blueprint.frameSizeMax = packet_size_max;
        blueprint.frameSizeMin = packet_size_min;
        generator.blueprint = blueprint;
    endtask

    task createEnvironment();
        reg_driver  = new("REG Driver", reg_generator.transMbx, REG);
        reg_driver.wordDelayEnable_wt = 8;
        reg_driver.wordDelayDisable_wt = 1;
        reg_driver.wordDelayLow = 5;
        reg_driver.wordDelayHigh = 10;
        driver  = new("Driver", generator.transMbx, RX);
        monitor = new("Monitor", MONITOR);
        responder = new("Responder", TX);
        // disable DST_RDY
        responder.wordDelayEnable_wt = 0;
        responder.wordDelayDisable_wt = 1;
        scoreboard = new;

        driver.setCallbacks(scoreboard.driverCbs);
        monitor.setCallbacks(scoreboard.monitorCbs);
    endtask

    task resetDesign();
        RESET=1;
        #RESET_TIME RESET = 0;
    endtask

    task enableTestEnvironment();
        reg_driver.setEnabled();
        driver.setEnabled();
        monitor.setEnabled();
        responder.setEnabled();
    endtask

    task disableTestEnvironment();
        wait(!driver.busy);
        do begin
            wait(!monitor.busy);
            fork : StayIdleWait
                wait(monitor.busy) disable StayIdleWait;
                #(100*CLK_PERIOD) disable StayIdleWait;
            join
        end while(monitor.busy);
        reg_driver.setDisabled();
        driver.setDisabled();
        monitor.setDisabled();
        responder.setDisabled();
    endtask

    task test1();
        $write("\n\n############ TEST CASE 1 ############\n\n");
        enableTestEnvironment();
        reg_generator.setEnabled(1000);
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
