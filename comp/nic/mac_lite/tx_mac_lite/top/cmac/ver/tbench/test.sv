/*!
 * \file test.sv
 * \brief Test Cases
 * \author Jakub Cabal <cabal@cesnet.cz>
 * \date 2017
 */
 /*
 * Copyright (C) 2017 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

import sv_common_pkg::*;
import sv_lbus_pkg::*;
import sv_flu_pkg::*;
import sv_mi32_pkg::*;
import test_pkg::*;

program TEST (
    output logic RESET,
    iFrameLinkURx.tb RX,
    iLbusTx.tb       TX,
    iMi32.tb         MI,
    iLbusTx.monitor  MONITOR
);

    FrameLinkUTransaction blueprint;
    Generator generator;
    FrameLinkUDriver #(512,6,3)  driver;
    LbusResponder                responder;
    LbusMonitor                  monitor;
    Scoreboard #(TR_TABLE_FIRST_ONLY) scoreboard;

    task createGeneratorEnvironment(int packet_size_max, int packet_size_min);
        generator = new("Generator", 0);
        blueprint = new;
        blueprint.packetSizeMax = packet_size_max;
        blueprint.packetSizeMin = packet_size_min;
        generator.blueprint = blueprint;
    endtask

    task createEnvironment();
        driver  = new("Driver", generator.transMbx, RX);
        monitor = new("Monitor", MONITOR);
        responder = new("Responder", TX);
        scoreboard = new;
        driver.setCallbacks(scoreboard.driverCbs);
        monitor.setCallbacks(scoreboard.monitorCbs);
        responder.wordDelayEnable_wt = 2;
        responder.wordDelayDisable_wt = 8;
        responder.wordDelayLow = 6;
        responder.wordDelayHigh = 9;
        driver.insideTxDelayEn_wt     = 1;
        driver.insideTxDelayDisable_wt= 10;
        driver.insideTxDelayLow  = 0;
        driver.insideTxDelayHigh = 5;
    endtask

    task resetDesign();
        RESET=1;
        #RESET_TIME RESET = 0;
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
                #(100*FLU_CLK_PERIOD) disable StayIdleWait;
            join
        end while(monitor.busy);
        driver.setDisabled();
        monitor.setDisabled();
        responder.setDisabled();
    endtask

    task initObuf();
      automatic Mi32Transaction mi32Transaction = new();
      automatic Mi32Driver      mi32Driver      = new("Mi32 Driver", null, MI);

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

      #(10*FLU_CLK_PERIOD);
    endtask : initObuf

    task readFrameCounters();
     automatic Mi32Transaction mi32Transaction = new();
     automatic Mi32Driver      mi32Driver      = new("Mi32 Driver", null, MI);
     automatic Mi32Monitor     mi32Monitor     = new("Mi32 Monitor", MI);
     bit [63:0] trfc;    // Total Received Frames Counter
     bit [63:0] tsfc;    // Sent Frames Counter
     bit [63:0] cfc;     // Bytes Sent Counter
     bit [63:0] dfc;     // Discarded Frames Counter

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
     trfc[31:0]  = mi32Transaction.data;
      // High part
     mi32Transaction.address = 32'h10;
     mi32Monitor.executeTransaction(mi32Transaction);
     trfc[63:32] = mi32Transaction.data;

     // Read Sent Frames Counter
     // Low part
     mi32Transaction.address = 32'h0C;
     mi32Monitor.executeTransaction(mi32Transaction);
     tsfc[31:0]  = mi32Transaction.data;
     // High part
     mi32Transaction.address = 32'h1C;
     mi32Monitor.executeTransaction(mi32Transaction);
     tsfc[63:32] = mi32Transaction.data;

     // Read Bytes Sent Counter
      // Low part
     mi32Transaction.address = 32'h04;
     mi32Monitor.executeTransaction(mi32Transaction);
     cfc[31:0]  = mi32Transaction.data;
      // High part
     mi32Transaction.address = 32'h14;
     mi32Monitor.executeTransaction(mi32Transaction);
     cfc[63:32] = mi32Transaction.data;

     // Read Discarded Frames Counter
      // Low part
     mi32Transaction.address = 32'h08;
     mi32Monitor.executeTransaction(mi32Transaction);
     dfc[31:0]  = mi32Transaction.data;
      // High part
     mi32Transaction.address = 32'h18;
     mi32Monitor.executeTransaction(mi32Transaction);
     dfc[63:32] = mi32Transaction.data;

     #(20*FLU_CLK_PERIOD);

     // Display counters values
     $write("------------------------------------------------------------\n");
     $write("-- CMAC OBUF Frame Counters\n");
     $write("------------------------------------------------------------\n");
     $write("Total Frames Counter:     %10d\n",trfc);
     $write("Sent Frames Counter:      %10d\n",tsfc);
     $write("Sent Bytes Counter:       %10d\n",cfc);
     $write("Discarded Frames Counter: %10d\n",dfc);
     $write("------------------------------------------------------------\n");

    endtask : readFrameCounters

    task test1();
        $write("\n\n############ TEST CASE 1 ############\n\n");
        initObuf();
        enableTestEnvironment();
        generator.setEnabled(TRANSACTION_COUNT);
        wait(!generator.enabled);
        disableTestEnvironment();
        scoreboard.display();
        readFrameCounters();
    endtask

    initial begin
        resetDesign();
        createGeneratorEnvironment(FRAME_SIZE_MAX, FRAME_SIZE_MIN);
        createEnvironment();
        test1();
        $write("Verification finished successfully!\n");
        $stop();
    end

endprogram
