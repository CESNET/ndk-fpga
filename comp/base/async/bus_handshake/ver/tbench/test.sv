// test.sv
// Copyright (C) 2020 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

import sv_common_pkg::*;
import sv_mvb_pkg::*;
import test_pkg::*;

program TEST (
    input logic CLK,
    output logic RESET,
    iMvbRx.tb RX,
    iMvbTx.tb TX,
    iMvbTx.monitor MONITOR
);

    MvbTransaction #(DATA_WIDTH) blueprint;
    Generator generator;
    MvbDriver #(1,DATA_WIDTH) driver;
    MvbResponder #(1,DATA_WIDTH) responder;
    MvbMonitor #(1,DATA_WIDTH) monitor;
    Scoreboard scoreboard;


    task createGeneratorEnvironment();
        generator = new("Generator", 0);
        blueprint = new;
        generator.blueprint = blueprint;
    endtask

    task createEnvironment();
        driver  = new("Driver", generator.transMbx, RX);
        monitor = new("Monitor", MONITOR);
        responder = new("Responder", TX);
        scoreboard = new;
        driver.setCallbacks(scoreboard.driverCbs);
        monitor.setCallbacks(scoreboard.monitorCbs);
    endtask

    task resetDesign();
        RESET=1;
        #RESET_TIME RESET = 0;
    endtask

    task enableTestEnvironment();
        driver.setEnabled();
        responder.setEnabled();
    endtask

    task disableTestEnvironment();
        wait(!driver.busy);
        do begin
            wait(!monitor.busy);
            fork : StayIdleWait
                wait(monitor.busy) disable StayIdleWait;
                #(100*RX_CLK_PERIOD) disable StayIdleWait;
            join
        end while(monitor.busy);
        driver.setDisabled();
        monitor.setDisabled();
        responder.setDisabled();
    endtask


    task test1();
        $write("\n\n############ TEST CASE 1 ############\n\n");
        //driver.wordDelayEnable_wt = 0;
        //driver.wordDelayDisable_wt = 1;
        //responder.wordDelayEnable_wt = 0;
        //responder.wordDelayDisable_wt = 1;
        monitor.setEnabled();
        generator.setEnabled(TRANSACTION_COUNT);
        #(20*RX_CLK_PERIOD);
        #(555555*RX_CLK_PERIOD);
        RESET=1;
        wait(!generator.enabled);
        disableTestEnvironment();
        //scoreboard.display();
        //driver.setDisabled();
        //monitor.setDisabled();
        //responder.setDisabled();
    endtask

    task test2();
        $write("\n\n############ TEST CASE 2 ############\n\n");
        //driver.wordDelayEnable_wt = 0;
        //driver.wordDelayDisable_wt = 1;
        //responder.wordDelayEnable_wt = 0;
        //responder.wordDelayDisable_wt = 1;
        monitor.setEnabled();
        generator.setEnabled(TRANSACTION_COUNT);
        #(20*RX_CLK_PERIOD);
        wait(!generator.enabled);
        disableTestEnvironment();
        scoreboard.display();
    endtask


    initial begin
        createGeneratorEnvironment();
        createEnvironment();
        enableTestEnvironment();
        resetDesign();
        test1();
        createGeneratorEnvironment();
        createEnvironment();
        enableTestEnvironment();
        resetDesign();
        test2();
        $write("Verification finished successfully!\n");
        $stop();
    end

endprogram

