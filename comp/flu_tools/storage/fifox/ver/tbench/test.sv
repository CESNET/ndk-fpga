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
import sv_flu_pkg::*;
import test_pkg::*;



program TEST (
    input logic CLK,
    output logic RESET,
    iFrameLinkURx.tb RX,
    iFrameLinkUTx.tb TX,
    //iFrameLinkUFifo.ctrl CTRL,
    iFrameLinkURx.monitor MONITOR_RX,
    iFrameLinkUTx.monitor MONITOR_TX
);


    FrameLinkUTransaction fluBlueprint;
    Generator generator;
    FrameLinkUDriver #(DATA_WIDTH,EOP_POS_WIDTH,SOP_POS_WIDTH) fluDriver;
    FrameLinkUMonitor #(DATA_WIDTH,EOP_POS_WIDTH,SOP_POS_WIDTH) fluMonitor;
    FrameLinkUResponder #(DATA_WIDTH,EOP_POS_WIDTH,SOP_POS_WIDTH) fluResponder;
    //FrameLinkUFifoChecker #(DATA_WIDTH,EOP_POS_WIDTH,SOP_POS_WIDTH, BLOCK_SIZE,STATUS_WIDTH, ITEMS, USE_BRAMS) fluChecker;
    Scoreboard              scoreboard;


    task createGeneratorEnvironment(int packet_size_max = GENERATOR0_FLU_PACKET_SIZE_MAX, int packet_size_min = GENERATOR0_FLU_PACKET_SIZE_MIN);
        generator = new("Generator0", 0);
        fluBlueprint = new;
        fluBlueprint.packetSizeMax = packet_size_max;
        fluBlueprint.packetSizeMin = packet_size_min;
        generator.blueprint = fluBlueprint;
    endtask

    task createEnvironment();
        fluDriver  = new ("Driver0", generator.transMbx, RX);
        fluDriver.insideTxDelayEn_wt = DRIVER0_INSIDE_DELAYEN_WT;
        fluDriver.insideTxDelayDisable_wt = DRIVER0_INSIDE_DELAYDIS_WT;
        fluDriver.insideTxDelayLow = DRIVER0_INSIDE_DELAYLOW;
        fluDriver.insideTxDelayHigh = DRIVER0_INSIDE_DELAYHIGH;
        fluDriver.startPositionLow = DRIVER0_START_POS_LOW;
        fluDriver.startPositionHigh = DRIVER0_START_POS_HIGH;
        fluMonitor = new ("Monitor0", MONITOR_TX);
        fluResponder = new ("Responder0", TX);
        fluResponder.rxDelayEn_wt = MONITOR0_DELAYEN_WT;
        fluResponder.rxDelayDisable_wt = MONITOR0_DELAYDIS_WT;
        fluResponder.rxDelayLow  = MONITOR0_DELAYLOW;
        fluResponder.rxDelayHigh = MONITOR0_DELAYHIGH;
        fluResponder.insideRxDelayEn_wt = MONITOR0_INSIDE_DELAYEN_WT;
        fluResponder.insideRxDelayDisable_wt = MONITOR0_INSIDE_DELAYDIS_WT;
        fluResponder.insideRxDelayLow = MONITOR0_INSIDE_DELAYLOW;
        fluResponder.insideRxDelayHigh = MONITOR0_INSIDE_DELAYHIGH;
        //fluChecker = new("Checker0", MONITOR_RX, MONITOR_TX, CTRL);
        scoreboard = new;
        fluDriver.setCallbacks(scoreboard.driverCbs);
        fluMonitor.setCallbacks(scoreboard.monitorCbs);
    endtask

    task resetDesign();
        RESET=1;
        #RESET_TIME RESET = 0;
    endtask

    task enableTestEnvironment();
        fluDriver.setEnabled();
        fluMonitor.setEnabled();
        fluResponder.setEnabled();
        //fluChecker.setEnabled();
    endtask

    task disableTestEnvironment();
        #(1000*CLK_PERIOD);
        fluDriver.setDisabled();
        #(1000*CLK_PERIOD);
        fluMonitor.setDisabled();
        fluResponder.setDisabled();
        //fluChecker.setDisabled();
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
        createGeneratorEnvironment(8,1);
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
        fluResponder.rxDelayEn_wt            = 5;
        fluResponder.rxDelayDisable_wt       = 1;
        fluResponder.rxDelayLow              = 0;
        fluResponder.rxDelayHigh             = 10;
        fluResponder.insideRxDelayEn_wt      = 5;
        fluResponder.insideRxDelayDisable_wt = 1;
        fluResponder.insideRxDelayLow        = 0;
        fluResponder.insideRxDelayHigh       = 10;
        fluDriver.insideTxDelayEn_wt =0;
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
        fluResponder.rxDelayEn_wt        = 0;
        fluResponder.insideRxDelayEn_wt  = 0;
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
        fluResponder.rxDelayEn_wt            = 5;
        fluResponder.rxDelayDisable_wt       = 1;
        fluResponder.rxDelayLow              = 0;
        fluResponder.rxDelayHigh             = 4;
        fluResponder.insideRxDelayEn_wt      = 5;
        fluResponder.insideRxDelayDisable_wt = 1;
        fluResponder.insideRxDelayLow        = 0;
        fluResponder.insideRxDelayHigh       = 4;
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
        $stop();
    end

endprogram
