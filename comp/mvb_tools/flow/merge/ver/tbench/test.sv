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
    iMvbRx.tb RX[ITEMS],
    iMvbTx.tb TX,
    iMvbTx.monitor MONITOR
);


    MvbTransaction #(ITEM_WIDTH) blueprint;
    Generator generator[ITEMS];
    MvbDriver #(1,ITEM_WIDTH) driver[ITEMS];
    MvbResponder #(ITEMS,ITEM_WIDTH) responder;
    MvbMonitor #(ITEMS,ITEM_WIDTH) monitor;
    Scoreboard scoreboard;
    virtual iMvbRx#(1,ITEM_WIDTH).tb vRX[ITEMS];

    task createGeneratorEnvironment();
        foreach(generator[i]) begin
            generator[i] = new("Generator", 0);
            blueprint = new;
            generator[i].blueprint = blueprint;
        end
    endtask

    task createEnvironment();
        vRX = RX;
        scoreboard = new;
        foreach(driver[i]) begin
            driver[i]  = new("Driver", generator[i].transMbx, vRX[i]);
            driver[i].setCallbacks(scoreboard.driverCbs);
        end
        monitor = new("Monitor", MONITOR);
        monitor.setCallbacks(scoreboard.monitorCbs);
        responder = new("Responder", TX);
        if(!USE_DST_RDY) begin
            responder.wordDelayEnable_wt = 0;
            responder.wordDelayDisable_wt = 1;
        end
    endtask

    task resetDesign();
        RESET=1;
        #RESET_TIME RESET = 0;
    endtask

    task enableTestEnvironment();
        foreach(driver[i])
            driver[i].setEnabled();
        monitor.setEnabled();
        responder.setEnabled();
    endtask

    task disableTestEnvironment();
        foreach(driver[i])
            wait(!driver[i].busy);
        do begin
            wait(!monitor.busy);
            fork : StayIdleWait
                wait(monitor.busy) disable StayIdleWait;
                #(100*CLK_PERIOD) disable StayIdleWait;
            join
        end while(monitor.busy);
        foreach(driver[i])
            driver[i].setDisabled();
        monitor.setDisabled();
        responder.setDisabled();
    endtask


    task test1();
        $write("\n\n############ TEST CASE 1 ############\n\n");
        enableTestEnvironment();
        foreach(generator[i])
            generator[i].setEnabled(TRANSACTION_COUNT);
        foreach(generator[i])
            wait(!generator[i].enabled);
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
