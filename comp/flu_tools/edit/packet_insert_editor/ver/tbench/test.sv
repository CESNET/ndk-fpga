/*
 * test.sv: Automatic test
 * Copyright (C) 2015 CESNET
 * Author: Pavel Benacek <benacek@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 * TODO:
 *
 */

import sv_common_pkg::*;
import sv_flu_pkg::*;
import test_pkg::*;

// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
program TEST (
  input  logic           CLK,
  output logic           RESET,
  iFrameLinkUEditRx.tb   RX,
  iFrameLinkUTx.tb       TX,
  iFrameLinkUTx.monitor  MONITOR
  );

  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------

  // Transaction
  FrameLinkUEditTransaction #(OFFSET_WIDTH,EN_MASK) fluEditBlueprint;
  // Generator
  Generator                fluEditGenerator;
  // Driver
  FrameLinkUEditDriver #(DATA_WIDTH, EOP_POS_WIDTH, SOP_POS_WIDTH, OFFSET_WIDTH)  fluEditDriver;
  // Monitor
  FrameLinkUMonitor #(DATA_WIDTH, EOP_POS_WIDTH, SOP_POS_WIDTH)    fluMonitor;
  // Responder
  FrameLinkUResponder #(DATA_WIDTH, EOP_POS_WIDTH, SOP_POS_WIDTH)  fluResponder;
  // Scoreboard
  Scoreboard              scoreboard;

  // --------------------------------------------------------------------------
  //                       Creating Environment tasks
  // --------------------------------------------------------------------------

  // Create Test Environment
  task createEnvironment();
    // Create generator
    fluEditGenerator = new("Generator", 0);
      fluEditBlueprint = new;
      fluEditBlueprint.packetSizeMax = GENERATOR_FLU_PACKET_SIZE_MAX;
      fluEditBlueprint.packetSizeMin = GENERATOR_FLU_PACKET_SIZE_MIN;
      fluEditGenerator.blueprint     = fluEditBlueprint;
    // Create driver
    fluEditDriver  = new ("Driver", fluEditGenerator.transMbx, RX);
      fluEditDriver.insideTxDelayEn_wt       = DRIVER_INSIDE_DELAYEN_WT;
      fluEditDriver.insideTxDelayDisable_wt  = DRIVER_INSIDE_DELAYDIS_WT;
      fluEditDriver.insideTxDelayLow         = DRIVER_INSIDE_DELAYLOW;
      fluEditDriver.insideTxDelayHigh        = DRIVER_INSIDE_DELAYHIGH;
      fluEditDriver.startPositionLow         = DRIVER_START_POS_LOW;
      fluEditDriver.startPositionHigh        = DRIVER_START_POS_HIGH;
    // Create monitor
    fluMonitor = new ("Monitor", MONITOR);
    // Create responder
    fluResponder = new ("Responder", TX);
      fluResponder.rxDelayEn_wt            = MONITOR_DELAYEN_WT;
      fluResponder.rxDelayDisable_wt       = MONITOR_DELAYDIS_WT;
      fluResponder.rxDelayLow              = MONITOR_DELAYLOW;
      fluResponder.rxDelayHigh             = MONITOR_DELAYHIGH;
      fluResponder.insideRxDelayEn_wt      = MONITOR_INSIDE_DELAYEN_WT;
      fluResponder.insideRxDelayDisable_wt = MONITOR_INSIDE_DELAYDIS_WT;
      fluResponder.insideRxDelayLow        = MONITOR_INSIDE_DELAYLOW;
      fluResponder.insideRxDelayHigh       = MONITOR_INSIDE_DELAYHIGH;
    // Create scoreboard and register callbacks to driver and monitors
    scoreboard = new;
      fluEditDriver.setCallbacks(scoreboard.driverCbs);
      fluMonitor.setCallbacks(scoreboard.monitorCbs);
  endtask : createEnvironment

  // --------------------------------------------------------------------------
  //                       Test auxilarity procedures
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Resets design
  task resetDesign();
    RESET=1;                       // Init Reset variable
    #RESET_TIME     RESET = 0;     // Deactivate reset after reset_time
  endtask : resetDesign

  // --------------------------------------------------------------------------
  // Enable test Environment
  task enableTestEnvironment();
    fluEditDriver.setEnabled();
    fluMonitor.setEnabled();
    fluResponder.setEnabled();
  endtask : enableTestEnvironment

  // --------------------------------------------------------------------------
  // Disable test Environment
  task disableTestEnvironment();
    int i;
    #(10*CLK_PERIOD);
    i = 0;
    // Check if monitor is not receiving transaction for 100 CLK_PERIODs
    while (i<100) begin
      if (fluEditDriver.busy || fluMonitor.busy)
        i = 0;
      else
        i++;
      #(CLK_PERIOD);
    end

    // Disable drivers
    fluEditDriver.setDisabled();
    // Disable monitors
    fluMonitor.setDisabled();
    fluResponder.setDisabled();
  endtask : disableTestEnvironment

  // --------------------------------------------------------------------------
  //                            Test cases
  // --------------------------------------------------------------------------
  // Basic test
  task test1();
    $write("\n\n############ TEST CASE 1 ############\n\n");
    createEnvironment();
    enableTestEnvironment();
    fluEditGenerator.setEnabled(TRANSACTION_COUNT);
    wait (fluEditGenerator.enabled == 0);
    disableTestEnvironment();
    scoreboard.display();
  endtask: test1

  // Generate very short packets
  task test2();
    $write("\n\n############ TEST CASE 2 ############\n\n");
    createEnvironment();
    // ////////////////////////////////
    fluEditBlueprint = new();
    fluEditBlueprint.packetSizeMax = 64;
    fluEditBlueprint.packetSizeMin = 8;
    fluEditGenerator.blueprint = fluEditBlueprint;
    // ////////////////////////////////
    enableTestEnvironment();
    fluEditGenerator.setEnabled(TRANSACTION_COUNT*4);
    wait (fluEditGenerator.enabled == 0);
    disableTestEnvironment();
    scoreboard.display();
  endtask: test2

  // Classic length transactions, slow TX and fast RX
  task test3();
    $write("\n\n############ TEST CASE 3 ############\n\n");
    createEnvironment();
    // ////////////////////////////////
    fluResponder.insideRxDelayEn_wt      = 4;
    fluResponder.insideRxDelayDisable_wt = 2;
    fluResponder.insideRxDelayLow        = 4;
    fluResponder.insideRxDelayHigh       = 10;
    fluEditDriver.insideTxDelayEn_wt       = 1;
    fluEditDriver.insideTxDelayDisable_wt  = 10;
    fluEditDriver.insideTxDelayLow         = 0;
    fluEditDriver.insideTxDelayHigh        = 1;
    // ////////////////////////////////
    enableTestEnvironment();
    fluEditGenerator.setEnabled(TRANSACTION_COUNT);
    wait (fluEditGenerator.enabled == 0);
    disableTestEnvironment();
    scoreboard.display();
  endtask: test3


  // Classic length transactions, no TX wait
  task test4();
    $write("\n\n############ TEST CASE 4 ############\n\n");
    createEnvironment();
    // ////////////////////////////////
    fluResponder.rxDelayEn_wt            = 0;
    fluResponder.rxDelayDisable_wt       = 10;
    fluResponder.rxDelayLow              = 0;
    fluResponder.rxDelayHigh             = 0;
    // ////////////////////////////////
    enableTestEnvironment();
    fluEditGenerator.setEnabled(TRANSACTION_COUNT);
    wait (fluEditGenerator.enabled == 0);
    disableTestEnvironment();
    scoreboard.display();
  endtask: test4

  // Very short packets, lot of waiting
  task test5();
    $write("\n\n############ TEST CASE 5 ############\n\n");
    createEnvironment();
    // ////////////////////////////////
    fluResponder.insideRxDelayEn_wt      = 4;
    fluResponder.insideRxDelayDisable_wt = 1;
    fluResponder.insideRxDelayLow        = 4;
    fluResponder.insideRxDelayHigh       = 10;
    fluEditDriver.insideTxDelayEn_wt       = 1;
    fluEditDriver.insideTxDelayDisable_wt  = 10;
    fluEditDriver.insideTxDelayLow         = 0;
    fluEditDriver.insideTxDelayHigh        = 1;
    fluEditBlueprint = new();
    fluEditBlueprint.packetSizeMax = 64;
    fluEditBlueprint.packetSizeMin = 8;
    fluEditGenerator.blueprint = fluEditBlueprint;
    // ////////////////////////////////
    enableTestEnvironment();
    fluEditGenerator.setEnabled(TRANSACTION_COUNT);
    wait (fluEditGenerator.enabled == 0);
    disableTestEnvironment();
    scoreboard.display();
  endtask: test5

  // --------------------------------------------------------------------------
  //                           Main test part
  // --------------------------------------------------------------------------
  initial begin
    // -------------------------------------
    // DESIGN ENVIROMENT
    // -------------------------------------
    resetDesign(); // Reset design
    createEnvironment(); // Create Test Enviroment
    // -------------------------------------
    // TESTING
    // -------------------------------------
    test1();       // Run Test 1
    test2();
    test3();
    test4();
    test5();

    // -------------------------------------
    // STOP TESTING
    // -------------------------------------
    $stop();       // Stop testing
  end

endprogram

