/*!
 * \file test.sv
 * \brief Test Cases
 * \author Daniel Kriz <xkrizd01@vutbr.cz>
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
import sv_mfb_pkg::*;
import sv_mvb_pkg::*;
import test_pkg::*;

program TEST (
    input logic CLK,
    output logic RESET,
    iMfbRx RX,
    iMfbTx TX_MFB,
    iMvbTx TX_MVB
);

    MfbTransaction #(MFB_ITEM_WIDTH,MFB_META_WIDTH) blueprint;
    Generator generator;
    MfbDriver #(MFB_REGIONS,MFB_REGION_SIZE,MFB_BLOCK_SIZE,MFB_ITEM_WIDTH,0,MFB_META_WIDTH,MFB_META_ALIGNMENT) driver;
    MfbResponder #(MFB_REGIONS,MFB_REGION_SIZE,MFB_BLOCK_SIZE,MFB_ITEM_WIDTH,MFB_META_WIDTH,MFB_META_ALIGNMENT) responder;
    MfbMonitor #(MFB_REGIONS,MFB_REGION_SIZE,MFB_BLOCK_SIZE,MFB_ITEM_WIDTH,MFB_META_WIDTH,MFB_META_ALIGNMENT) monitor;
    MvbMonitor #(MVB_ITEMS,MFB_META_WIDTH) mvb_monitor;
    MvbResponder #(MVB_ITEMS,MFB_META_WIDTH) mvb_responder;
    Scoreboard scoreboard;

    task createGeneratorEnvironment(int packet_size_max, int packet_size_min);
        generator = new("Generator", 0);
        blueprint = new;
        blueprint.frameSizeMax = packet_size_max;
        blueprint.frameSizeMin = packet_size_min;
        generator.blueprint = blueprint;
    endtask

    task createEnvironment();
        driver  = new("Driver", generator.transMbx, RX);
        monitor = new("MFB Monitor", TX_MFB);
        responder = new("Responder", TX_MFB);

        mvb_monitor = new("MVB Monitor", TX_MVB);
        mvb_responder = new("Responder", TX_MVB);
        scoreboard = new;
        driver.setCallbacks(scoreboard.driverCbs);
        monitor.setCallbacks(scoreboard.monitorCbs);
        mvb_monitor.setCallbacks(scoreboard.mvb_monitorCbs);
    endtask

    task resetDesign();
        RESET=1;
        #RESET_TIME RESET = 0;
    endtask

    task enableTestEnvironment();
        driver.setEnabled();
        responder.setEnabled();
        mvb_responder.setEnabled();
    endtask

    task disableTestEnvironment();
        wait(!driver.busy);
        do begin
            wait(!(monitor.busy || mvb_monitor.busy));
            fork : StayIdleWait
                wait(monitor.busy || mvb_monitor.busy) disable StayIdleWait;
                #(100*CLK_PERIOD) disable StayIdleWait;
            join
        end while(monitor.busy || mvb_monitor.busy);
    endtask

    task test1();
        $write("\n\n############ TEST CASE 1 ############\n\n");
        monitor.setEnabled();
        mvb_monitor.setEnabled();
        generator.setEnabled(TRANSACTION_COUNT);
        wait(!generator.enabled);
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
