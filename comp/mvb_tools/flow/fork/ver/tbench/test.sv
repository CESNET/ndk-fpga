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
import test_pkg::*;

program TEST (
    input logic CLK,
    output logic RESET,
    iMvbRx.tb RX,
    iMvbTx.tb TX[OUTPUT_PORTS],
    iMvbTx.monitor MONITOR[OUTPUT_PORTS]
);

    MvbTransaction #(ITEM_WIDTH) blueprint;
    Generator generator;
    MvbDriver #(ITEMS,ITEM_WIDTH) driver;
    MvbResponder #(ITEMS,ITEM_WIDTH) responder[OUTPUT_PORTS];
    MvbMonitor #(ITEMS,ITEM_WIDTH) monitor[OUTPUT_PORTS];
    Scoreboard scoreboard;
    virtual iMvbTx #(ITEMS,ITEM_WIDTH).tb vTX[OUTPUT_PORTS];
    virtual iMvbTx #(ITEMS,ITEM_WIDTH).monitor vMONITOR[OUTPUT_PORTS];

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
            monitor[i].setCallbacks(scoreboard.monitorCbs[i]);
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
        foreach(responder[i]) begin
            responder[i].setEnabled();
        end
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
        foreach(monitor[i]) begin
            monitor[i].setDisabled();
        end
        foreach(responder[i]) begin
            responder[i].setDisabled();
        end
    endtask

    task test1();
        $write("\n\n############ TEST CASE 1 ############\n\n");
        foreach(monitor[i]) begin
            monitor[i].setEnabled();
        end
        generator.setEnabled(TRANSACTION_COUNT);
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
        $write("Verification finished successfully!\n");
        $stop();
    end

endprogram
