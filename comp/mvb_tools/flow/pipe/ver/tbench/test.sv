/*!
 * \file test.sv
 * \brief Test Cases
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2016
 */
 /*
 * Copyright (C) 2016 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

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


    MvbTransaction #(ITEM_WIDTH) blueprint;
    Generator generator;
    MvbDriver #(ITEMS,ITEM_WIDTH) driver;
    MvbResponder #(ITEMS,ITEM_WIDTH) responder;
    MvbMonitor #(ITEMS,ITEM_WIDTH) monitor;
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
        if(!USE_DST_RDY) begin
            responder.wordDelayEnable_wt = 0;
            responder.wordDelayDisable_wt = 1;
        end
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
        test1();
        $write("Verification finished successfully!\n");
        $stop();
    end

endprogram
