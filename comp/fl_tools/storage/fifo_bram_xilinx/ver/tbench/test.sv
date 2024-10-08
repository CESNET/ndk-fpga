/*!
 * \file test.sv
 * \brief Test Cases
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2016
 */
 /*
 * Copyright (C) 2016 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

import sv_common_pkg::*;
import sv_fl_pkg::*;
import test_pkg::*;



program TEST (
    input logic CLK,
    output logic RESET,
    iFrameLinkRx.tb RX,
    iFrameLinkTx.tb TX,
    //iFrameLinkUFifo.ctrl CTRL,
    iFrameLinkTx.monitor MONITOR_TX
);


    FrameLinkTransaction flBlueprint;
    Generator generator;
    FrameLinkDriver #(DATA_WIDTH,DREM_WIDTH) flDriver;
    FrameLinkMonitor #(DATA_WIDTH,DREM_WIDTH) flMonitor;
    FrameLinkResponder #(DATA_WIDTH,DREM_WIDTH) flResponder;
    //FrameLinkUFifoChecker #(DATA_WIDTH,EOP_POS_WIDTH,SOP_POS_WIDTH, BLOCK_SIZE,STATUS_WIDTH, ITEMS, USE_BRAMS) flChecker;
    Scoreboard              scoreboard;


    task createGeneratorEnvironment(int parts = GENERATOR0_FL_PACKET_COUNT, int packet_size_max[] = GENERATOR0_FL_PACKET_SIZE_MAX, int packet_size_min[] = GENERATOR0_FL_PACKET_SIZE_MIN);
        generator = new("Generator0", 0);
        flBlueprint = new;
        flBlueprint.packetCount = parts;
        flBlueprint.packetSizeMax = packet_size_max;
        flBlueprint.packetSizeMin = packet_size_min;
        generator.blueprint = flBlueprint;
    endtask

    task createEnvironment();
        flDriver  = new ("Driver0", generator.transMbx, RX);
        flDriver.txDelayEn_wt = DRIVER0_DELAYEN_WT;
        flDriver.txDelayDisable_wt = DRIVER0_DELAYDIS_WT;
        flDriver.txDelayLow = DRIVER0_DELAYLOW;
        flDriver.txDelayHigh = DRIVER0_DELAYHIGH;
        flDriver.insideTxDelayEn_wt = DRIVER0_INSIDE_DELAYEN_WT;
        flDriver.insideTxDelayDisable_wt = DRIVER0_INSIDE_DELAYDIS_WT;
        flDriver.insideTxDelayLow = DRIVER0_INSIDE_DELAYLOW;
        flDriver.insideTxDelayHigh = DRIVER0_INSIDE_DELAYHIGH;
        flMonitor = new ("Monitor0", MONITOR_TX);
        flResponder = new ("Responder0", TX);
        flResponder.rxDelayEn_wt = MONITOR0_DELAYEN_WT;
        flResponder.rxDelayDisable_wt = MONITOR0_DELAYDIS_WT;
        flResponder.rxDelayLow = MONITOR0_DELAYLOW;
        flResponder.rxDelayHigh = MONITOR0_DELAYHIGH;
        flResponder.insideRxDelayEn_wt = MONITOR0_INSIDE_DELAYEN_WT;
        flResponder.insideRxDelayDisable_wt = MONITOR0_INSIDE_DELAYDIS_WT;
        flResponder.insideRxDelayLow = MONITOR0_INSIDE_DELAYLOW;
        flResponder.insideRxDelayHigh = MONITOR0_INSIDE_DELAYHIGH;
        //flChecker = new("Checker0", MONITOR_RX, MONITOR_TX, CTRL);
        scoreboard = new;
        flDriver.setCallbacks(scoreboard.driverCbs);
        flMonitor.setCallbacks(scoreboard.monitorCbs);
    endtask

    task resetDesign();
        RESET=1;
        #RESET_TIME RESET = 0;
    endtask

    task enableTestEnvironment();
        flDriver.setEnabled();
        flMonitor.setEnabled();
        flResponder.setEnabled();
        //flChecker.setEnabled();
    endtask

    task disableTestEnvironment();
        #(1000*CLK_PERIOD);
        flDriver.setDisabled();
        #(1000*CLK_PERIOD);
        flMonitor.setDisabled();
        flResponder.setDisabled();
        //flChecker.setDisabled();
    endtask


    task test1();
        $write("\n\n############ TEST CASE 1 ############\n\n");
        enableTestEnvironment();
        generator.setEnabled(TRANSACTION_COUNT);
        wait(!generator.enabled);
        disableTestEnvironment();
        scoreboard.display();
    endtask

    task test2();
        $write("\n\n############ TEST CASE 2 ############\n\n");
        createGeneratorEnvironment(2,'{4,8},'{1,1});
        createEnvironment();
        enableTestEnvironment();
        generator.setEnabled(TRANSACTION_COUNT);
        wait(!generator.enabled);
        disableTestEnvironment();
        scoreboard.display();
    endtask

    task test3();
        $write("\n\n############ TEST CASE 3 ############\n\n");
        createGeneratorEnvironment();
        createEnvironment();
        flResponder.rxDelayEn_wt            = 5;
        flResponder.rxDelayDisable_wt       = 1;
        flResponder.rxDelayLow              = 0;
        flResponder.rxDelayHigh             = 10;
        flResponder.insideRxDelayEn_wt      = 5;
        flResponder.insideRxDelayDisable_wt = 1;
        flResponder.insideRxDelayLow        = 0;
        flResponder.insideRxDelayHigh       = 10;
        flDriver.insideTxDelayEn_wt =0;
        enableTestEnvironment();
        generator.setEnabled(TRANSACTION_COUNT);
        wait(!generator.enabled);
        #(10000*CLK_PERIOD);
        disableTestEnvironment();
        scoreboard.display();
    endtask

    task test4();
        $write("\n\n############ TEST CASE 4 ############\n\n");
        createGeneratorEnvironment();
        createEnvironment();
        flResponder.rxDelayEn_wt        = 0;
        flResponder.insideRxDelayEn_wt  = 0;
        enableTestEnvironment();
        generator.setEnabled(TRANSACTION_COUNT);
        wait(!generator.enabled);
        disableTestEnvironment();
        scoreboard.display();
    endtask

    task test5();
        $write("\n\n############ TEST CASE 5 ############\n\n");
        createGeneratorEnvironment();
        createEnvironment();
        flResponder.rxDelayEn_wt            = 5;
        flResponder.rxDelayDisable_wt       = 1;
        flResponder.rxDelayLow              = 0;
        flResponder.rxDelayHigh             = 4;
        flResponder.insideRxDelayEn_wt      = 5;
        flResponder.insideRxDelayDisable_wt = 1;
        flResponder.insideRxDelayLow        = 0;
        flResponder.insideRxDelayHigh       = 4;
        enableTestEnvironment();
        generator.setEnabled(TRANSACTION_COUNT);
        wait(!generator.enabled);
        #(2000*CLK_PERIOD);
        disableTestEnvironment();
        scoreboard.display();
    endtask


    initial begin
        resetDesign();
        createGeneratorEnvironment();
        createEnvironment();
        test1();
        test2();
        test3();
        test4();
        test5();
        $write("Verification finished successfully!\n");
        $stop();
    end

endprogram
