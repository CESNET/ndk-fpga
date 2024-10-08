/*!
 * \file test.sv
 * \brief Test Cases
 * \author Daniel Kříž <xkrizd01@vutbr.cz>
 * \date 2020
 */
 /*
 * Copyright (C) 2020 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

import sv_common_pkg::*;
import sv_mvb_pkg::*;
import sv_mi32_pkg::*;
import test_pkg::*;



program TEST (
    input logic CLK,
    output logic RESET,
    iMi32.tb MI,
    iMvbRx.tb RX,
    iMvbTx.tb TX,
    iMvbTx.monitor MONITOR
);
    byte unsigned register[SRC_CHANNELS][4] = '{default:0};

    MvbTransaction #(NEW_RX_ITEM_WIDTH) blueprint;
    Generator generator;
    MvbDriver #(ITEMS,NEW_RX_ITEM_WIDTH) driver;
    MvbResponder #(ITEMS,NEW_TX_ITEM_WIDTH) responder;
    MvbMonitor #(ITEMS,NEW_TX_ITEM_WIDTH) monitor;

    Mi32Driver  mi32Driver;
    Mi32Monitor mi32Monitor;

    Scoreboard scoreboard;

    task registerSettings();
        // Generate default values to register
        if(REG_SETTINGS == 0) begin
            for (int i = 0; i < SRC_CHANNELS; i++) begin
                register[i][0] = 10;
                register[i][1] = 0;
                register[i][2] = 15;
                register[i][3] = 4;
            end
        end

        if(REG_SETTINGS == 1) begin
            for (int i = 4; i < SRC_CHANNELS; i++) begin
                register[i][0] = 10;
                register[i][1] = 0;
                register[i][2] = 15;
                register[i][3] = 4;
            end
                register[0][0] = 1;
                register[1][0] = SRC_CHANNELS;
                register[2][0] = 1;
                register[3][0] = SRC_CHANNELS;

                register[0][1] = 4;
                register[1][1] = 3;
                register[2][1] = 1;
                register[3][1] = SRC_CHANNELS;

                register[0][2] = 7;
                register[1][2] = 6;
                register[2][2] = 1;
                register[3][2] = SRC_CHANNELS;

                register[0][3] = 4;
                register[1][3] = 4;
                register[2][3] = 4;
                register[3][3] = 4;
        end

        if(REG_SETTINGS == 2) begin
            for (int i = 4; i < SRC_CHANNELS; i++) begin
                register[i][0] = 10;
                register[i][1] = 0;
                register[i][2] = 15;
                register[i][3] = 4;
            end
                register[0][0] = 0;
                register[1][0] = 20;
                register[2][0] = 128;
                register[3][0] = 255;
                register[0][1] = 0;
                register[1][1] = 1;
                register[2][1] = 0;
                register[3][1] = 0;
                register[0][2] = 255;
                register[1][2] = 128;
                register[2][2] = 255;
                register[3][2] = 255;
                register[0][3] = 4;
                register[1][3] = 4;
                register[2][3] = 4;
                register[3][3] = 4;
        end

        if(REG_SETTINGS == 3) begin
            for (int i = 0; i < SRC_CHANNELS; i++) begin
                register[i][0] = (i+1)*i;
                register[i][1] = i;
                register[i][2] = i+32-1;
                register[i][3] = 4;
            end
        end
    endtask

    task createGeneratorEnvironment();
        registerSettings();
        generator = new("Generator", 0);
        blueprint = new;
        generator.blueprint = blueprint;
    endtask

    task createEnvironment();
        driver  = new("MVB Driver", generator.transMbx, RX);
        monitor = new("MVB Monitor", MONITOR);
        responder = new("MVB Responder", TX);

        responder.wordDelayEnable_wt = 0;
        responder.wordDelayDisable_wt = 1;

        mi32Driver = new("Mi32 Driver", null, MI);
        mi32Monitor = new("Mi32 Monitor", MI);

        scoreboard = new(register);

        driver.setCallbacks(scoreboard.driverCbs);
        monitor.setCallbacks(scoreboard.monitorCbs);
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
            fork : StayIdleWait
                wait(monitor.busy) disable StayIdleWait;
                #(100*CLK_PERIOD) disable StayIdleWait;
            join
        end while(monitor.busy);
        driver.setDisabled();
        monitor.setDisabled();
        responder.setDisabled();
    endtask

    task initRegConfig();
        Mi32Transaction mi32_tr;

        // Set MI32 transaction
        mi32_tr = new();
        mi32_tr.rw = 1;
        mi32_tr.be = '1;

        for (int i = 0; i < SRC_CHANNELS; i++) begin
            // Send low 32 bits
            mi32_tr.address = 4*i;
            { << byte {mi32_tr.data}} = register[i][0:3];
            mi32Driver.sendTransaction(mi32_tr);
        end
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
        createGeneratorEnvironment();
        createEnvironment();
        initRegConfig();
        test1();
        $write("Verification finished successfully!\n");
        $stop();
    end

endprogram
