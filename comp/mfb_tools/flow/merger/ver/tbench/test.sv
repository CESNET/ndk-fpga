/*!
* \file test.sv
* \brief Test Cases
* author: Jakub Cabal <cabal@cesnet.cz>
* Copyright (C) 2018 CESNET z. s. p. o.
*
* LICENSE TERMS
* SPDX-License-Identifier: BSD-3-Clause
*
*/

import sv_common_pkg::*;
import sv_mvb_pkg::*;
import sv_mfb_pkg::*;
import test_pkg::*;

program TEST (
    input  logic CLK,
    output logic RESET,
    iMvbRx.tb RX_MVB[MERGER_INPUTS-1:0],
    iMfbRx.tb RX_MFB[MERGER_INPUTS-1:0],
    iMvbTx.tb TX_MVB,
    iMfbTx.tb TX_MFB,
    iMvbTx.monitor MO_MVB,
    iMfbTx.monitor MO_MFB
);

    virtual iMvbRx #(MVB_ITEMS,MVB_ITEM_WIDTH)                                              vRX_MVB[MERGER_INPUTS-1:0] = RX_MVB;
    virtual iMfbRx #(MFB_REGIONS,MFB_REG_SIZE,MFB_BLOCK_SIZE,MFB_ITEM_WIDTH,MFB_META_WIDTH) vRX_MFB[MERGER_INPUTS-1:0] = RX_MFB;

    CustomTransaction #(MVB_ITEM_WIDTH,MFB_ITEM_WIDTH,MFB_META_WIDTH) blueprint;
    CustomTransGenerator                                              generator [MERGER_INPUTS-1:0];

    MvbDriver    #(MVB_ITEMS,MVB_ITEM_WIDTH)                                                mvb_driver [MERGER_INPUTS-1:0];
    MfbDriver    #(MFB_REGIONS,MFB_REG_SIZE,MFB_BLOCK_SIZE,MFB_ITEM_WIDTH,0,MFB_META_WIDTH) mfb_driver [MERGER_INPUTS-1:0];

    MvbResponder #(MVB_ITEMS,MVB_ITEM_WIDTH) mvb_responder;
    MvbMonitor   #(MVB_ITEMS,MVB_ITEM_WIDTH) mvb_monitor;

    MfbResponder #(MFB_REGIONS,MFB_REG_SIZE,MFB_BLOCK_SIZE,MFB_ITEM_WIDTH,MFB_META_WIDTH) mfb_responder;
    MfbMonitor   #(MFB_REGIONS,MFB_REG_SIZE,MFB_BLOCK_SIZE,MFB_ITEM_WIDTH,MFB_META_WIDTH) mfb_monitor;

    Scoreboard scoreboard;

    task createEnvironment(int dataSizeMax, int dataSizeMin);
        blueprint = new();
        blueprint.dataSizeMax = dataSizeMax;
        blueprint.dataSizeMin = dataSizeMin;

        scoreboard = new;

        for (int i = 0; i < MERGER_INPUTS; i++) begin

             generator[i] = new($sformatf("Custom Generator %03d",i),i);
             generator[i].blueprint = blueprint;
             generator[i].setCallbacks(scoreboard.generatorCbs);

             mvb_driver[i] = new($sformatf("MVB Driver %03d",i), generator[i].mvbTransMbx, vRX_MVB[i]);
             mfb_driver[i] = new($sformatf("MFB Driver %03d",i), generator[i].mfbTransMbx, vRX_MFB[i]);

             mvb_driver[i].wordDelayEnable_wt  =     RX_MVB_SRC_RDY_FALL_CHANCE[i];
             mvb_driver[i].wordDelayDisable_wt = 100-RX_MVB_SRC_RDY_FALL_CHANCE[i];
             mfb_driver[i].wordDelayEnable_wt  =     RX_MFB_SRC_RDY_FALL_CHANCE[i];
             mfb_driver[i].wordDelayDisable_wt = 100-RX_MFB_SRC_RDY_FALL_CHANCE[i];

             mfb_driver[i].mode = mfb_driver[i].MODE_RANDOM;

             mvb_driver[i].wordDelayHigh = RX_MVB_SRC_RDY_FALL_TIME_MAX[i];
             mfb_driver[i].wordDelayHigh = RX_MFB_SRC_RDY_FALL_TIME_MAX[i];

        end

        mvb_responder = new("Responder MVB", TX_MVB);
        mfb_responder = new("Responder MFB", TX_MFB);

        mvb_responder.wordDelayEnable_wt  =     TX_MVB_DST_RDY_FALL_CHANCE;
        mvb_responder.wordDelayDisable_wt = 100-TX_MVB_DST_RDY_FALL_CHANCE;
        mfb_responder.wordDelayEnable_wt  =     TX_MFB_DST_RDY_FALL_CHANCE;
        mfb_responder.wordDelayDisable_wt = 100-TX_MFB_DST_RDY_FALL_CHANCE;

        mvb_responder.wordDelayHigh = TX_MVB_DST_RDY_FALL_TIME_MAX;
        mfb_responder.wordDelayHigh = TX_MFB_DST_RDY_FALL_TIME_MAX;

        mvb_monitor = new("Monitor MVB", MO_MVB);
        mfb_monitor = new("Monitor MFB", MO_MFB);

        mvb_monitor.setCallbacks(scoreboard.monitorCbs);
        mfb_monitor.setCallbacks(scoreboard.monitorCbs);
    endtask

    task resetDesign();
        RESET=1;
        #RESET_TIME RESET = 0;
    endtask

    task enableTestEnvironment();
        scoreboard.setEnabled();

        for (int i = 0; i < MERGER_INPUTS; i++) begin
             mvb_driver[i].setEnabled();
             mfb_driver[i].setEnabled();
        end

        mvb_monitor.setEnabled();
        mfb_monitor.setEnabled();
        mvb_responder.setEnabled();
        mfb_responder.setEnabled();
    endtask

    task disableTestEnvironment();
        automatic int busy = 1;

        wait(!mvb_driver[0].busy && !mfb_driver[0].busy);
        do begin
            wait(!mvb_monitor.busy && !mfb_monitor.busy);

            fork : StayIdleWait0
                wait(mvb_monitor.busy || mfb_monitor.busy) disable StayIdleWait0;
                #(100*CLK_PERIOD) disable StayIdleWait0;
            join

            busy = 0;
            for (int i = 0; i < MERGER_INPUTS; i++)
                busy |= mvb_driver[i].busy || mfb_driver[i].busy;

        end while(mvb_monitor.busy || mfb_monitor.busy || busy);

        for (int i = 0; i < MERGER_INPUTS; i++) begin
            mvb_driver[i].setDisabled();
            mfb_driver[i].setDisabled();
        end

        mfb_monitor.setDisabled();
        mfb_responder.setDisabled();
        mvb_monitor.setDisabled();
        mvb_responder.setDisabled();
        scoreboard.setDisabled();
    endtask

    task test1();
        automatic int transactions = 0;
        automatic int remaining    = TRANSACTION_COUNT;
        $write("\n\n############ TEST CASE 1 ############\n\n");
        enableTestEnvironment();

        for (int i = 0; i < MERGER_INPUTS; i++) begin
            if (i == MERGER_INPUTS-1)
                transactions = remaining;
            else
                transactions = TRANSACTION_COUNT / MERGER_INPUTS;
            generator[i].setEnabled(transactions);
            remaining -= transactions;
        end

        for (int i = 0; i < MERGER_INPUTS; i++)
            wait(!generator[i].enabled);

        disableTestEnvironment();
        scoreboard.display();
        if (scoreboard.scoreTable.tr_table.size() > 0) begin
            $write("ERROR: Scoreboard table not empty! Some transactions did not pass!\n");
            $stop;
        end
    endtask

    initial begin
        resetDesign();
        createEnvironment(FRAME_SIZE_MAX, FRAME_SIZE_MIN);
        test1();
        $write("Verification finished successfully!\n");
        $stop();
    end

endprogram
