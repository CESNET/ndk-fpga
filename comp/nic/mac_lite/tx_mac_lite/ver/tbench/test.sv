// test.sv
// Copyright (C) 2019 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

import sv_common_pkg::*;
import sv_mfb_pkg::*;
import sv_mi32_pkg::*;
import test_pkg::*;
import crc32_ethernet_pkg::*;

program TEST (
    input  logic RX_CLK,
    input  logic RX_CLK_X2,
    output logic RX_RESET,
    input  logic TX_CLK,
    output logic TX_RESET,
    input  logic MI_CLK,
    output logic MI_RESET,
    iMfbRx.tb RX,
    iMfbTx.tb TX,
    iMfbTx.monitor MONITOR,
    iMi32.tb  MI32
);

    MfbTransaction #(RX_ITEM_WIDTH)                                         blueprint;
    Generator                                                               generator;
    MfbDriver      #(RX_REGIONS,RX_REGION_SIZE,RX_BLOCK_SIZE,RX_ITEM_WIDTH) driver;
    MfbResponder   #(TX_REGIONS,TX_REGION_SIZE,TX_BLOCK_SIZE,TX_ITEM_WIDTH) responder;
    MfbMonitor     #(TX_REGIONS,TX_REGION_SIZE,TX_BLOCK_SIZE,TX_ITEM_WIDTH) monitor;
    Scoreboard                                                              scoreboard;

    task createGeneratorEnvironment(int packet_size_max, int packet_size_min);
        generator = new("Generator", 0);
        blueprint = new;
        blueprint.frameSizeMax = packet_size_max;
        blueprint.frameSizeMin = packet_size_min;
        generator.blueprint = blueprint;
    endtask

    task createEnvironment();
        driver  = new("Driver", generator.transMbx, RX);
        monitor = new("Monitor", MONITOR);
        responder = new("Responder", TX);
        scoreboard = new;
        driver.setCallbacks(scoreboard.driverCbs);
        monitor.setCallbacks(scoreboard.monitorCbs);

        driver.wordDelayEnable_wt = 2;
        driver.wordDelayDisable_wt = 8;
        driver.wordDelayLow = 0;
        driver.wordDelayHigh = 6;

        if (RX_INCLUDE_IPG) begin
            $write("RX MFB stream is include IPG (RX_INCLUDE_IPG=True)!\n");
            driver.ifgEnable_wt = 1;
            driver.ifgDisable_wt = 0;
            driver.ifgLow = 4+13; // 4 bytes for CRC, 13 bytes for IPG
            driver.ifgHigh = 20;
        end
    endtask

    task resetDesign();
        RX_RESET=1;
        TX_RESET=1;
        MI_RESET=1;
        #RESET_TIME
        RX_RESET=0;
        TX_RESET=0;
        MI_RESET=0;
    endtask

    task enableTestEnvironment();
        driver.setEnabled();
        monitor.setEnabled();
        responder.setEnabled();
    endtask

    task disableTestEnvironment();
        wait(!driver.busy);
        do begin
            wait(!monitor.busy);
            fork : StayIdleWait
                wait(monitor.busy) disable StayIdleWait;
                #(400*TX_CLK_PERIOD) disable StayIdleWait;
            join
        end while(monitor.busy);
        driver.setDisabled();
        monitor.setDisabled();
        responder.setDisabled();
    endtask

    task initObuf();
        Mi32Transaction mi32Transaction ;
        Mi32Driver      mi32Driver      ;
        mi32Transaction = new();
        mi32Driver      = new("Mi32 Driver", null, MI32);

        // Disable OBUF
        mi32Transaction.rw      = 1;
        mi32Transaction.be      = '1;
        mi32Transaction.address = 32'h20;
        mi32Transaction.data    = 32'h0;
        mi32Driver.sendTransaction(mi32Transaction);

        // Enable OBUF
        mi32Transaction.rw      = 1;
        mi32Transaction.be      = '1;
        mi32Transaction.address = 32'h20;
        mi32Transaction.data    = 32'h1;
        mi32Driver.sendTransaction(mi32Transaction);

        #(10*TX_CLK_PERIOD);
    endtask

    task readFrameCounters();
        longint total, bytes, discarded, sent;

        bit [63:0] tpfc;    // Total Processed Frames Counter
        bit [63:0] tsfc;    // Total Sent Frames Counter
        bit [63:0] toc;     // Bytes Sent Counter
        bit [63:0] dfc;     // Discarded Frames Counter

        Mi32Transaction mi32Transaction ;
        Mi32Driver      mi32Driver      ;
        Mi32Monitor     mi32Monitor     ;
        mi32Transaction = new();
        mi32Driver      = new("Mi32 Driver", null, MI32);
        mi32Monitor     = new("Mi32 Monitor", MI32);

        // Sample the current frame counters values
        mi32Transaction.address = 32'h2C;
        mi32Transaction.data    = 32'h1;
        mi32Transaction.rw      = 1;
        mi32Transaction.be      = '1;
        mi32Driver.sendTransaction(mi32Transaction);

        mi32Transaction.rw      = 0;
        mi32Transaction.be      = '1;

        // Read Total Received Frames Counter
        // Low part
        mi32Transaction.address = 32'h00;
        mi32Monitor.executeTransaction(mi32Transaction);
        tpfc[31:0]  = mi32Transaction.data;
        // High part
        mi32Transaction.address = 32'h10;
        mi32Monitor.executeTransaction(mi32Transaction);
        tpfc[63:32] = mi32Transaction.data;

        // Read Octects Frames Counter
        // Low part
        mi32Transaction.address = 32'h04;
        mi32Monitor.executeTransaction(mi32Transaction);
        toc[31:0]  = mi32Transaction.data;
        // High part
        mi32Transaction.address = 32'h14;
        mi32Monitor.executeTransaction(mi32Transaction);
        toc[63:32] = mi32Transaction.data;

        // Read Discarded Frames Counter
        // Low part
        mi32Transaction.address = 32'h08;
        mi32Monitor.executeTransaction(mi32Transaction);
        dfc[31:0]  = mi32Transaction.data;
        // High part
        mi32Transaction.address = 32'h18;
        mi32Monitor.executeTransaction(mi32Transaction);
        dfc[63:32] = mi32Transaction.data;

        // Read Total Sent Frames Counter
        // Low part
        mi32Transaction.address = 32'h0c;
        mi32Monitor.executeTransaction(mi32Transaction);
        tsfc[31:0]  = mi32Transaction.data;
        // High part
        mi32Transaction.address = 32'h1c;
        mi32Monitor.executeTransaction(mi32Transaction);
        tsfc[63:32] = mi32Transaction.data;

        #(20*TX_CLK_PERIOD);

        // Display counters values
        $write("------------------------------------------------------------\n");
        $write("-- TX MAC LITE Frame Counters\n");
        $write("------------------------------------------------------------\n");
        $write("Total Processed Frames Counter: \t\t %10d\n",tpfc);
        $write("Total Sent Frames Counter:      \t\t %10d\n",tsfc);
        $write("Bytes Sent Counter:             \t\t %10d\n",toc);
        $write("Discarded Frames Counter:       \t\t %10d\n",dfc);
        $write("------------------------------------------------------------\n");

        // Compare expected and read values
        bytes = scoreboard.getByteCounter();
        discarded = scoreboard.getDiscardedFramesCounter();
        sent = scoreboard.getSentFramesCounter();
        total = discarded + sent;

        if (bytes != toc) begin
            $write("Mismatch in expected and read byte counter!\n");
            $stop();
        end

        // Detected and expected number of discarded frames
        if (discarded != dfc) begin
            $write("Mismatch in expected and read discarded frames counter!\n");
            $stop();
        end

        // Detected and expected number of sent frames
        if (sent != tsfc) begin
            $write("Mismatch in expected and read sent frames counter!\n");
            $stop();
        end

        // Detected and expected number of processed frames
        if (total != tpfc) begin
            $write("Mismatch in expected and read processed frames counter!\n");
            $stop();
        end
    endtask

    task test1();
        $write("\n\n############ TEST CASE 1 ############\n\n");
        initObuf();
        enableTestEnvironment();
        generator.setEnabled(TRANSACTION_COUNT);
        wait(!generator.enabled);
        disableTestEnvironment();
        scoreboard.display();
        readFrameCounters();
        $write("Verification finished successfully!\n");
    endtask

    initial begin
        resetDesign();
        createGeneratorEnvironment(FRAME_SIZE_MAX, FRAME_SIZE_MIN);
        createEnvironment();
        test1();
        $stop();
    end

endprogram
