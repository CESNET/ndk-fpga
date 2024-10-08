/*
 * test.sv: FL_BINDER automatic test
 * Copyright (C) 2008 CESNET
 * Author(s): Martin Kosek <kosek@liberouter.org>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 */

import sv_common_pkg::*;
import sv_fl_pkg::*;
import test_pkg::*;

// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
program TEST (
  input  logic     CLK,
  output logic     RESET,
  iFrameLinkRx.tb  RX[INPUT_COUNT],
  iFrameLinkTx.tb  TX,
  iFrameLinkTx.monitor  MONITOR
  );

  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------
  FrameLinkTransaction                                                flBlueprint;
  Generator                                                           generator[INPUT_COUNT];
  FrameLinkDriver  #(DRIVER_DATA_WIDTH, DRIVER_DREM_WIDTH)            flDriver[INPUT_COUNT];
  FrameLinkMonitor #(MONITOR_DATA_WIDTH, MONITOR_DREM_WIDTH)          flMonitor;
  FrameLinkResponder #(MONITOR_DATA_WIDTH, MONITOR_DREM_WIDTH)        flResponder;
  Coverage #(INPUT_WIDTH,INPUT_DREM_WIDTH,OUTPUT_WIDTH,OUTPUT_DREM_WIDTH) coverage;
  Scoreboard #(INPUT_COUNT)                                           scoreboard;

  // Only array of virtual interfaces can be indexed
  virtual iFrameLinkRx.tb #(DRIVER_DATA_WIDTH, DRIVER_DREM_WIDTH) vRX[INPUT_COUNT];

  // --------------------------------------------------------------------------
  //                       Creating Environment tasks
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Create Test Environment
  task createGeneratorEnvironment(int packet_count = GENERATOR_FL_PACKET_COUNT,
                                  int packet_size_max[] = GENERATOR_FL_PACKET_SIZE_MAX,
                                  int packet_size_min[] = GENERATOR_FL_PACKET_SIZE_MIN
                                  );
    // Create generators
    for(int i=0; i<INPUT_COUNT; i++) begin
      string generatorLabel;

      generatorLabel = $sformatf("RX Generator %0d", i);
      generator[i]= new(generatorLabel, i);
      flBlueprint = new;
      flBlueprint.packetCount   = packet_count;
      flBlueprint.packetSizeMax = packet_size_max;
      flBlueprint.packetSizeMin = packet_size_min;
      generator[i].blueprint = flBlueprint;
    end;
  endtask: createGeneratorEnvironment

  // Create Test Environment
  task createEnvironment();
    // Assign virtual interfaces
    vRX      = RX;
    // Coverage class
    coverage = new();
    // Create scoreboard
    scoreboard = new;

    // Create and connect driver
    for(int i=0; i<INPUT_COUNT; i++) begin
      string driverLabel;


      driverLabel = $sformatf("Driver %0d", i);
      flDriver[i]    = new (driverLabel, generator[i].transMbx, vRX[i]);
      flDriver[i].txDelayEn_wt             = DRIVER_DELAYEN_WT;
      flDriver[i].txDelayDisable_wt        = DRIVER_DELAYDIS_WT;
      flDriver[i].txDelayLow               = DRIVER_DELAYLOW;
      flDriver[i].txDelayHigh              = DRIVER_DELAYHIGH;
      flDriver[i].insideTxDelayEn_wt       = DRIVER_INSIDE_DELAYEN_WT;
      flDriver[i].insideTxDelayDisable_wt  = DRIVER_INSIDE_DELAYDIS_WT;
      flDriver[i].insideTxDelayLow         = DRIVER_INSIDE_DELAYLOW;
      flDriver[i].insideTxDelayHigh        = DRIVER_INSIDE_DELAYHIGH;
      flDriver[i].setCallbacks(scoreboard.driverCbs);
      coverage.addFrameLinkInterfaceRx(vRX[i],"RX coverage");
    end

    // Create and connect monitor and responder
    flMonitor   = new ("Monitor 0", TX);
    flResponder = new ("Responder 0", TX);
      flResponder.rxDelayEn_wt            = MONITOR_DELAYEN_WT;
      flResponder.rxDelayDisable_wt       = MONITOR_DELAYDIS_WT;
      flResponder.rxDelayLow              = MONITOR_DELAYLOW;
      flResponder.rxDelayHigh             = MONITOR_DELAYHIGH;
      flResponder.insideRxDelayEn_wt      = MONITOR_INSIDE_DELAYEN_WT;
      flResponder.insideRxDelayDisable_wt = MONITOR_INSIDE_DELAYDIS_WT;
      flResponder.insideRxDelayLow        = MONITOR_INSIDE_DELAYLOW;
      flResponder.insideRxDelayHigh       = MONITOR_INSIDE_DELAYHIGH;
      flMonitor.setCallbacks(scoreboard.monitorCbs);
      coverage.addFrameLinkInterfaceTx(MONITOR,"TX coverage");

  endtask : createEnvironment

  // --------------------------------------------------------------------------
  //                       Test auxilarity procedures
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Resets design
  task resetDesign();
    #(2*CLK_PERIOD);               // wait before reset
    RESET=1;                       // Init Reset variable
    #RESET_TIME     RESET = 0;     // Deactivate reset after reset_time
  endtask : resetDesign

  // --------------------------------------------------------------------------
  // Enable test Enviroment
  task enableTestEnvironment();
    // Enable Driver, Monitor, Coverage for each port
    for(int i=0; i<INPUT_COUNT; i++)
      flDriver[i].setEnabled();

    // enable Monitor and Responder
    flMonitor.setEnabled();
    flResponder.setEnabled();
    coverage.setEnabled();
  endtask : enableTestEnvironment

  // --------------------------------------------------------------------------
  // Disable test Enviroment
  task disableTestEnvironment();
    // Disable drivers
    #(1000*CLK_PERIOD);
    for(int i=0; i<INPUT_COUNT; i++)
      flDriver[i].setDisabled();

    // disable Monitor and Responder
    #(12000*CLK_PERIOD);
    flMonitor.setDisabled();
    flResponder.setDisabled();

    // Disable monitors
    coverage.setDisabled();
  endtask : disableTestEnvironment

  // --------------------------------------------------------------------------
  //                            Test cases
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Test Case 1
  // Long transactions
  task test1();
    $write("\n\n############ TEST CASE 1 ############\n\n");

    // create & enable environment
    createGeneratorEnvironment();
    createEnvironment();
    enableTestEnvironment();

    // Run generators
    for(int i=0; i<INPUT_COUNT; i++) begin
      generator[i].setEnabled(TEST_TRANSACTION_COUNT);
    end

   // wait until all generators are disabled
   for(int i=0; i<INPUT_COUNT; i++) begin
     wait (generator[i].enabled == 0);
   end

   // Disable Test Enviroment
   disableTestEnvironment();

   // Display Scoreboard
   scoreboard.display();
   coverage.display();
  endtask: test1

  // --------------------------------------------------------------------------
  // Test Case 2
  // short transactions
  task test2();
    $write("\n\n############ TEST CASE 2 ############\n\n");

    // create & enable environment
    createGeneratorEnvironment(FRAME_PARTS,'{8, 8, 8},'{1, 1, 1});
    createEnvironment();
    enableTestEnvironment();

    // Run generators
    for(int i=0; i<INPUT_COUNT; i++) begin
      generator[i].setEnabled(TEST_TRANSACTION_COUNT);
    end

    // wait until all generators are disabled
    for(int i=0; i<INPUT_COUNT; i++) begin
      wait (generator[i].enabled == 0);
    end

    // Disable Test Enviroment
    disableTestEnvironment();

    // Display Scoreboard
    scoreboard.display();
    coverage.display();
  endtask: test2

  // --------------------------------------------------------------------------
  // Test Case 3
  // Classic length transactions, no TX wait
  task test3();
    $write("\n\n############ TEST CASE 3 ############\n\n");

    // create & enable environment
    createGeneratorEnvironment();
    createEnvironment();

    // set zero delays
    flResponder.rxDelayEn_wt        = 0;
    flResponder.insideRxDelayEn_wt  = 0;

    // Enable Test environment
    enableTestEnvironment();

    // Run generators
    for(int i=0; i<INPUT_COUNT; i++) begin
      generator[i].setEnabled(TEST_TRANSACTION_COUNT);
    end

    // wait until all generators are disabled
    for(int i=0; i<INPUT_COUNT; i++) begin
      wait (generator[i].enabled == 0);
    end

    // Disable Test Enviroment
    disableTestEnvironment();

    // Display Scoreboard
    scoreboard.display();
    coverage.display();
  endtask: test3

  // --------------------------------------------------------------------------
  // Test Case 4
  // Classic length transactions, lot of waiting
  task test4();
    $write("\n\n############ TEST CASE 4 ############\n\n");

    // create & enable environment
    createGeneratorEnvironment();
    createEnvironment();

    // set zero delays
    flResponder.rxDelayEn_wt            = 5;
    flResponder.rxDelayDisable_wt       = 1;
    flResponder.rxDelayLow              = 0;
    flResponder.rxDelayHigh             = 4;
    flResponder.insideRxDelayEn_wt      = 5;
    flResponder.insideRxDelayDisable_wt = 1;
    flResponder.insideRxDelayLow        = 0;
    flResponder.insideRxDelayHigh       = 4;

    // Enable Test environment
    enableTestEnvironment();

    // Run generators
    for(int i=0; i<INPUT_COUNT; i++) begin
      generator[i].setEnabled(TEST_TRANSACTION_COUNT);
    end

    // wait until all generators are disabled
    for(int i=0; i<INPUT_COUNT; i++) begin
      wait (generator[i].enabled == 0);
    end

    // Disable Test Enviroment
    disableTestEnvironment();

    // Display Scoreboard
    scoreboard.display();
    coverage.display();
  endtask: test4

  // --------------------------------------------------------------------------
  //                           Main test part
  // --------------------------------------------------------------------------
  initial begin
    // prepare design enviroment
    resetDesign();

    // run all tests
    test1();
    test2();
    test3();
    test4();

    // stop test
    $write("Verification finished successfully!\n");
    $stop();
  end

endprogram

