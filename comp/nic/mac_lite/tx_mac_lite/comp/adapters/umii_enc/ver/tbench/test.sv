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

    iMfbRx.tb      MFB,
    iMiiTx.tb      MII
);
    MfbTransaction                                         mfb_blueprint;
    Generator                                              mfb_generator;
    MfbDriver #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) mfb_driver;

    MiiMonitor #(MII_DATA_WIDTH,MII_LANE_WIDTH) mii_monitor;

    Scoreboard scoreboard;

    task createGeneratorEnvironment(int frame_size_max, int frame_size_min);
        mfb_generator = new("MFB Generator", 0);
        mfb_blueprint = new;
        mfb_blueprint.frameSizeMax = frame_size_max;
        mfb_blueprint.frameSizeMin = frame_size_min;
        mfb_generator.blueprint = mfb_blueprint;
    endtask

   task createEnvironment();
        scoreboard = new();

        mfb_driver = new("MFB Driver", mfb_generator.transMbx, MFB);
        mfb_driver.setCallbacks(scoreboard.driverCbs);
        mfb_driver.wordDelayEnable_wt = 0;
        mfb_driver.wordDelayDisable_wt = 1;
        mfb_driver.ifgEnable_wt = 1;
        mfb_driver.ifgDisable_wt = 0;
        mfb_driver.ifgLow = 10;
        mfb_driver.ifgHigh = 63;

        mii_monitor = new ("MII Monitor", MII);
        mii_monitor.setCallbacks(scoreboard.monitorCbs);
    endtask

    task resetDesign();
        ASYNC_RESET = 1;
        #RESET_TIME ASYNC_RESET = 0;
    endtask

    task enableTestEnvironment();
        mfb_driver.setEnabled();
        mii_monitor.setEnabled();
    endtask

    task disableTestEnvironment();
        wait(!mfb_driver.busy);
        do begin
            wait(!mii_monitor.busy);
            fork : StayIdleWait0
                wait(mii_monitor.busy) disable StayIdleWait0;
                #(100*CLK_PERIOD) disable StayIdleWait0;
            join
        end while(mii_monitor.busy);
        mfb_driver.setDisabled();
        mii_monitor.setDisabled();
    endtask

    task test();
        $write("\n\n############ TEST CASE ############\n\n");
        enableTestEnvironment();
        mfb_generator.setEnabled(TRANSACTION_COUNT);
        wait(!mfb_generator.enabled);
        disableTestEnvironment();
        scoreboard.display();
    endtask

    initial begin
        for (int i = 0; i < FRAME_SIZE_MAX.size(); i++) begin
            resetDesign();
            createGeneratorEnvironment(FRAME_SIZE_MAX[i], FRAME_SIZE_MIN[i]);
            createEnvironment();
            test();
        end
        $write("Verification finished successfully!\n");
        $stop();
    end

endprogram
