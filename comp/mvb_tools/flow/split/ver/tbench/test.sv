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
    iMvbTx.tb TX[ITEMS],
    iMvbTx.monitor MONITOR[ITEMS]
);


    MvbTransaction #(ITEM_WIDTH) blueprint;
    Generator generator;
    MvbDriver #(ITEMS,ITEM_WIDTH) driver;
    MvbResponder #(1,ITEM_WIDTH) responder[ITEMS];
    MvbMonitor #(1,ITEM_WIDTH) monitor[ITEMS];
    Scoreboard scoreboard;
    virtual iMvbTx#(1,ITEM_WIDTH).tb vTX[ITEMS];
    virtual iMvbTx#(1,ITEM_WIDTH).monitor vMONITOR[ITEMS];

    task createGeneratorEnvironment();
        generator = new("Generator", 0);
        blueprint = new;
        generator.blueprint = blueprint;
    endtask

    task createEnvironment();
        scoreboard = new;
        vTX = TX;
        vMONITOR = MONITOR;
        driver  = new("Driver", generator.transMbx, RX);
        driver.setCallbacks(scoreboard.driverCbs);
        foreach(monitor[i]) begin
            monitor[i] = new("Monitor", vMONITOR[i]);
            monitor[i].setCallbacks(scoreboard.monitorCbs);
        end
        foreach(responder[i]) begin
            responder[i] = new("Responder", vTX[i]);
            if(!USE_DST_RDY) begin
                responder[i].wordDelayEnable_wt = 0;
                responder[i].wordDelayDisable_wt = 1;
            end
        end
    endtask

    task resetDesign();
        RESET=1;
        #RESET_TIME RESET = 0;
    endtask

    task enableTestEnvironment();
        driver.setEnabled();
        foreach(monitor[i])
            monitor[i].setEnabled();
        foreach(responder[i])
            responder[i].setEnabled();
    endtask

    task disableTestEnvironment();
        wait(!driver.busy);
        do begin
            wait(!monitor[0].busy);
            fork : StayIdleWait
                wait(monitor[0].busy) disable StayIdleWait;
                #(100*CLK_PERIOD) disable StayIdleWait;
            join
        end while(monitor[0].busy);
        driver.setDisabled();
        foreach(monitor[i])
            monitor[i].setDisabled();
        foreach(responder[i])
            responder[i].setDisabled();
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
