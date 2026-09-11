/*!
 * \file test.sv
 * \brief Test Cases
 * \author Jakub Cabal <xcabal05@stud.feec.vutbr.cz>
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
import test_pkg::*;

program TEST (
    input  logic CLK,
    output logic RESET,
    iMfbRx.tb      RX_MFB[MERGER_INPUTS],
    iMfbTx         TX_MFB,
    iMfbTx.monitor MONITOR
);

    virtual iMfbRx #(MFB_REGIONS,MFB_REGION_SIZE,MFB_BLOCK_SIZE,MFB_ITEM_WIDTH,MFB_META_WIDTH) vRX_MFB[MERGER_INPUTS] = RX_MFB;

    MfbTransaction #(MFB_ITEM_WIDTH,MFB_META_WIDTH) blueprint;
    Generator generator[MERGER_INPUTS-1:0];
    MfbDriver #(MFB_REGIONS,MFB_REGION_SIZE,MFB_BLOCK_SIZE,MFB_ITEM_WIDTH,0,MFB_META_WIDTH) driver[MERGER_INPUTS-1:0];
    MfbResponder #(MFB_REGIONS,MFB_REGION_SIZE,MFB_BLOCK_SIZE,MFB_ITEM_WIDTH,MFB_META_WIDTH) responder;
    MfbMonitor #(MFB_REGIONS,MFB_REGION_SIZE,MFB_BLOCK_SIZE,MFB_ITEM_WIDTH,MFB_META_WIDTH) monitor;
    Scoreboard scoreboard;

    task createGeneratorEnvironment(int packet_size_max, int packet_size_min);
        blueprint = new;
        blueprint.frameSizeMax = packet_size_max;
        blueprint.frameSizeMin = packet_size_min;

        for (int i = 0; i < MERGER_INPUTS; i++) begin
            generator[i] = new($sformatf("Generator %0d", i), i);
            generator[i].blueprint = blueprint;
        end
    endtask

    task createEnvironment();
        scoreboard = new;

        for (int i = 0; i < MERGER_INPUTS; i++) begin
            driver[i] = new($sformatf("Driver %0d", i), generator[i].transMbx, vRX_MFB[i]);
            driver[i].wordDelayEnable_wt  =     RX_MFB_SRC_RDY_FALL_CHANCE[i];
            driver[i].wordDelayDisable_wt = 100-RX_MFB_SRC_RDY_FALL_CHANCE[i];
            driver[i].wordDelayHigh       =     RX_MFB_SRC_RDY_FALL_TIME_MAX[i];
            driver[i].mode                = driver[i].MODE_RANDOM;
            driver[i].setCallbacks(scoreboard.driverCbs);
        end

        responder = new("Responder", TX_MFB);
        responder.wordDelayEnable_wt  =     TX_MFB_DST_RDY_FALL_CHANCE;
        responder.wordDelayDisable_wt = 100-TX_MFB_DST_RDY_FALL_CHANCE;
        responder.wordDelayHigh       =     TX_MFB_DST_RDY_FALL_TIME_MAX;

        monitor = new("Monitor", MONITOR);
        monitor.setCallbacks(scoreboard.monitorCbs);
    endtask

    task resetDesign();
        RESET = 1;
        #RESET_TIME RESET = 0;
    endtask

    task enableTestEnvironment();
        for (int i = 0; i < MERGER_INPUTS; i++) begin
            driver[i].setEnabled();
        end
        responder.setEnabled();
        monitor.setEnabled();
    endtask

    task disableTestEnvironment();
        automatic int busy = 1;

        // Wait until no driver is still busy sending.
        do begin
            busy = 0;
            for (int i = 0; i < MERGER_INPUTS; i++)
                busy |= driver[i].busy;
            if (busy) @(CLK);
        end while (busy);

        // Let the monitor drain the remaining frames.
        do begin
            wait(!monitor.busy);
            fork : StayIdleWait0
                wait(monitor.busy) disable StayIdleWait0;
                #(100*CLK_PERIOD) disable StayIdleWait0;
            join
        end while(monitor.busy);

        for (int i = 0; i < MERGER_INPUTS; i++) begin
            driver[i].setDisabled();
        end
        monitor.setDisabled();
        responder.setDisabled();
    endtask

    // Distributes the total transaction count across all inputs using increasing
    // weights (input i gets weight i+1). The last input receives the remainder so
    // that the sum is exactly TRANSACTION_COUNT. For MERGER_INPUTS=2 this yields a
    // roughly 33/67 split, preserving the original uneven-load intent that stresses
    // the round-robin arbitration.
    task test1();
        automatic int unsigned total_w = 0;
        automatic int unsigned acc     = 0;
        automatic int          trans   = 0;

        $write("\n\n############ TEST CASE 1 ############\n\n");
        enableTestEnvironment();
        resetDesign();

        for (int i = 0; i < MERGER_INPUTS; i++)
            total_w += (i+1);

        for (int i = 0; i < MERGER_INPUTS; i++) begin
            if (i == MERGER_INPUTS-1)
                trans = TRANSACTION_COUNT - acc;
            else begin
                trans = (TRANSACTION_COUNT * (i+1)) / total_w;
                acc  += trans;
            end
            generator[i].setEnabled(trans);
        end

        for (int i = 0; i < MERGER_INPUTS; i++)
            wait(!generator[i].enabled);

        disableTestEnvironment();
        scoreboard.display();
    endtask

    initial begin
        createGeneratorEnvironment(FRAME_SIZE_MAX, FRAME_SIZE_MIN);
        createEnvironment();
        test1();
        if (scoreboard.done()) begin
            $write("Verification finished successfully!\n");
        end
        $stop();
    end

endprogram
