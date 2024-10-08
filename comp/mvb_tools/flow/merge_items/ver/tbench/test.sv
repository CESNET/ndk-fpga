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
    iMvbRx.tb RX0,
    iMvbRx.tb RX1,
    iMvbTx.tb TX,
    iMvbTx.monitor MONITOR
);

    MvbTransaction #(RX0_ITEM_WIDTH) blueprint0;
    MvbTransaction #(RX1_ITEM_WIDTH) blueprint1;
    Generator generator0;
    Generator generator1;
    MvbDriver #(RX0_ITEMS,RX0_ITEM_WIDTH) driver0;
    MvbDriver #(RX1_ITEMS,RX1_ITEM_WIDTH) driver1;
    MvbResponder #(RX0_ITEMS,RX0_ITEM_WIDTH+RX1_ITEM_WIDTH) responder;
    MvbMonitor #(RX0_ITEMS,RX0_ITEM_WIDTH+RX1_ITEM_WIDTH) monitor;
    Scoreboard scoreboard;

    task createGeneratorEnvironment();
        generator0 = new("Generator0", 0);
        generator1 = new("Generator1", 0);
        blueprint0 = new;
        blueprint1 = new;
        generator0.blueprint = blueprint0;
        generator1.blueprint = blueprint1;
    endtask

    task createEnvironment();
        driver0  = new("Driver0", generator0.transMbx, RX0);
        driver1  = new("Driver1", generator1.transMbx, RX1);
        monitor = new("Monitor", MONITOR);
        responder = new("Responder", TX);

        scoreboard = new;
        driver0.setCallbacks(scoreboard.driverCbs0);
        driver1.setCallbacks(scoreboard.driverCbs1);
        monitor.setCallbacks(scoreboard.monitorCbs);
    endtask

    task resetDesign();
        RESET=1;
        #RESET_TIME RESET = 0;
    endtask

    task enableTestEnvironment();
        driver0.setEnabled();
        driver1.setEnabled();
        monitor.setEnabled();
        responder.setEnabled();
    endtask

    task disableTestEnvironment();
        wait(!driver1.busy && !driver0.busy);
        do begin
            wait(!monitor.busy);
            fork : StayIdleWait
                wait(monitor.busy) disable StayIdleWait;
                #(100*CLK_PERIOD) disable StayIdleWait;
            join
        end while(monitor.busy);
        driver0.setDisabled();
        driver1.setDisabled();
        monitor.setDisabled();
        responder.setDisabled();
    endtask

    task test1();
        $write("\n\n############ TEST CASE 1 ############\n\n");
        enableTestEnvironment();
        generator0.setEnabled(TRANSACTION_COUNT);
        generator1.setEnabled(TRANSACTION_COUNT);
        wait(!generator0.enabled && !generator1.enabled);
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
