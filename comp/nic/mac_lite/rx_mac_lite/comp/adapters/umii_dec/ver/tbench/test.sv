// test.sv
// Copyright (C) 2019 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

import sv_common_pkg::*;
import sv_mii_pkg::*;
import sv_mfb_pkg::*;
import test_pkg::*;
`include "scoreboard.sv"

program TEST (
    input  logic CLK,
    output logic ASYNC_RESET,

    iMiiRx.tb      MII,
    iMfbTx.tb      MFB,
    iMfbTx.monitor MFB_MONITOR
);
    MiiTransaction                 mii_blueprint;
    Generator                      mii_generator;
    MiiDriver #(MII_DATA_WIDTH,MII_LANE_WIDTH) mii_driver;

    MfbResponder #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) mfb_responder;
    MfbMonitor   #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) mfb_monitor;

    Scoreboard scoreboard;

    task createGeneratorEnvironment(int frame_size_max, int frame_size_min);
        mii_generator = new("MII Generator", 0);
        mii_blueprint = new;
        mii_blueprint.dataSizeMax = frame_size_max;
        mii_blueprint.dataSizeMin = frame_size_min;
        mii_generator.blueprint = mii_blueprint;
    endtask

   task createEnvironment(int index);
        scoreboard = new(index);

        mii_driver = new("MII Driver", mii_generator.transMbx, MII);
        mii_driver.setCallbacks(scoreboard.miiDriverCbs);

        mfb_responder = new("MFB Responder", MFB);
        // disable MFB_DST_RDY
        mfb_responder.wordDelayEnable_wt = 0;
        mfb_responder.wordDelayDisable_wt = 1;
        mfb_monitor   = new("MFB Monitor", MFB_MONITOR);
        mfb_monitor.setCallbacks(scoreboard.mfbMonitorCbs);
    endtask

    task resetDesign();
        ASYNC_RESET = 1;
        #RESET_TIME ASYNC_RESET = 0;
    endtask

    task enableTestEnvironment();
        mii_driver.setEnabled();
        mfb_monitor.setEnabled();
        mfb_responder.setEnabled();
    endtask

    task disableTestEnvironment();
        wait(!mii_driver.busy);
        do begin
            wait(!mfb_monitor.busy);
            fork : StayIdleWait0
                wait(mfb_monitor.busy) disable StayIdleWait0;
                #(100*CLK_PERIOD) disable StayIdleWait0;
            join
        end while(mfb_monitor.busy);
        mii_driver.setDisabled();
        mfb_monitor.setDisabled();
        mfb_responder.setDisabled();
    endtask

    task test(int test_mode);
        $write("\n\n############ TEST CASE ############\n\n");
        enableTestEnvironment();
        mii_generator.setEnabled(TRANSACTION_COUNT);
        wait(!mii_generator.enabled);
        disableTestEnvironment();
        if (test_mode == 0) begin
            $write("Verification of stability done!\n\n");
        end else begin
            scoreboard.display();
        end
    endtask

    initial begin
        for (int i = 0; i < FRAME_SIZE_MAX.size(); i++) begin
            resetDesign();
            createGeneratorEnvironment(FRAME_SIZE_MAX[i], FRAME_SIZE_MIN[i]);
            createEnvironment(i);
            test(TRANSACTION_CHECK[i]);
        end
        $write("Verification finished successfully!\n");
        $stop();
    end

endprogram
