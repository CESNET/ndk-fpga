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
    iMvbRx RX,
    iMvbTx TX
);

    MvbTransaction #(DATA_WIDTH) blueprint;
    Generator generator;
    MvbDriver #(INPUTS,DATA_WIDTH) driver;
    MvbResponder #(OUTPUTS,DATA_WIDTH) responder;
    MvbMonitor #(OUTPUTS,DATA_WIDTH) monitor;
    Scoreboard scoreboard;

    task createGeneratorEnvironment();
        generator = new("Generator", 0);
        blueprint = new;
        generator.blueprint = blueprint;
    endtask

    task createEnvironment();
        driver  = new("Driver", generator.transMbx, RX);
        monitor = new("Monitor", TX);
        responder = new("Responder", TX);

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
        driver.setEnabled();
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
        responder.setDisabled();
    endtask

    task test1();
        $write("\n\n############ TEST CASE 1 ############\n\n");
        monitor.setEnabled();
        generator.setEnabled(TRANSACTION_COUNT);
        wait(!generator.enabled);
        disableTestEnvironment();
        monitor.setDisabled();
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
