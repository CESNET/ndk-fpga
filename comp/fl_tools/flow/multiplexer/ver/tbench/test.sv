/*
 * test.sv: FL_MULTIPLEXER automatic test
 * Copyright (C) 2010 CESNET
 * Author(s): Marek Santa <santa@liberouter.org>
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
  iFrameLinkRx.tb  RX[CHANNELS],
  iFrameLinkTx.tb  TX[CHANNELS],
  iFrameLinkTx.monitor  MONITOR[CHANNELS]
  );

  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------
  FrameLinkTransaction                              flBlueprint;
  Generator                                         generator[CHANNELS];
  FrameLinkDriver  #(DRIVER_DATA_WIDTH, DRIVER_DREM_WIDTH)
                                                    flDriver[CHANNELS];
  FrameLinkMonitor #(MONITOR_DATA_WIDTH, MONITOR_DREM_WIDTH)
                                                    flMonitor[CHANNELS];
  FrameLinkResponder #(MONITOR_DATA_WIDTH, MONITOR_DREM_WIDTH)
                                                    flResponder[CHANNELS];
  Coverage #(DATA_WIDTH,DREM_WIDTH,DATA_WIDTH,DREM_WIDTH) coverage;
  Scoreboard                                        scoreboard[CHANNELS];

  // Only array of virtual interfaces can be indexed
  virtual iFrameLinkRx.tb #(DRIVER_DATA_WIDTH, DRIVER_DREM_WIDTH)
                                                           vRX[CHANNELS];
  virtual iFrameLinkTx.tb #(MONITOR_DATA_WIDTH, MONITOR_DREM_WIDTH)
                                                           vTX[CHANNELS];
  virtual iFrameLinkTx.monitor #(MONITOR_DATA_WIDTH, MONITOR_DREM_WIDTH)
                                                           vMONITOR[CHANNELS];

  // --------------------------------------------------------------------------
  //                       Creating Environment tasks
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Create Test Environment
  task createGeneratorEnvironment(int packet_count = GENERATOR_PACKET_COUNT,
                                  int packet_size_max[] = GENERATOR_PACKET_SIZE_MAX,
                                  int packet_size_min[] = GENERATOR_PACKET_SIZE_MIN
                                  );
    // Create generators
    for(int i=0; i<CHANNELS; i++) begin
      string generatorLabel;

      generatorLabel = $sformatf( "RX Generator %0d", i);
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
    vTX      = TX;
    vMONITOR = MONITOR;

    // Coverage class
    coverage = new();

    // Create scoreboard
    for(int i=0; i<CHANNELS; i++) begin
      string scoreboardLabel;

      scoreboardLabel = $sformatf( "Scoreboard %0d", i);
      scoreboard[i] = new(scoreboardLabel);
    end

    // Create and connect driver
    for(int i=0; i<CHANNELS; i++) begin
      string driverLabel;

      driverLabel = $sformatf( "Driver %0d", i);
      flDriver[i]    = new (driverLabel, generator[i].transMbx, vRX[i]);
      flDriver[i].txDelayEn_wt             = DRIVER_DELAYEN_WT;
      flDriver[i].txDelayDisable_wt        = DRIVER_DELAYDIS_WT;
      flDriver[i].txDelayLow               = DRIVER_DELAYLOW;
      flDriver[i].txDelayHigh              = DRIVER_DELAYHIGH;
      flDriver[i].insideTxDelayEn_wt       = DRIVER_INSIDE_DELAYEN_WT;
      flDriver[i].insideTxDelayDisable_wt  = DRIVER_INSIDE_DELAYDIS_WT;
      flDriver[i].insideTxDelayLow         = DRIVER_INSIDE_DELAYLOW;
      flDriver[i].insideTxDelayHigh        = DRIVER_INSIDE_DELAYHIGH;
      flDriver[i].setCallbacks(scoreboard[i].driverCbs);
      coverage.addFrameLinkInterfaceRx(vRX[i],"RX coverage");
    end

    // Create and connect monitor and responder
    for(int i=0; i<CHANNELS; i++) begin
      string monitorLabel;
      string responderLabel;

      monitorLabel = $sformatf( "Monitor %0d", i);
      responderLabel = $sformatf( "Responder %0d", i);
      flMonitor[i]   = new (monitorLabel, vMONITOR[i]);
      flResponder[i] = new (responderLabel, vTX[i]);
        flResponder[i].rxDelayEn_wt            = MONITOR_DELAYEN_WT;
        flResponder[i].rxDelayDisable_wt       = MONITOR_DELAYDIS_WT;
        flResponder[i].rxDelayLow              = MONITOR_DELAYLOW;
        flResponder[i].rxDelayHigh             = MONITOR_DELAYHIGH;
        flResponder[i].insideRxDelayEn_wt      = MONITOR_INSIDE_DELAYEN_WT;
        flResponder[i].insideRxDelayDisable_wt = MONITOR_INSIDE_DELAYDIS_WT;
        flResponder[i].insideRxDelayLow        = MONITOR_INSIDE_DELAYLOW;
        flResponder[i].insideRxDelayHigh       = MONITOR_INSIDE_DELAYHIGH;
        flMonitor[i].setCallbacks(scoreboard[i].monitorCbs);
      coverage.addFrameLinkInterfaceTx(vMONITOR[i],"TX coverage");
    end

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
    for(int i=0; i<CHANNELS; i++)
      flDriver[i].setEnabled();

    // enable Monitor and Responder
    for(int i=0; i<CHANNELS; i++) begin
      flMonitor[i].setEnabled();
      flResponder[i].setEnabled();
    end

    coverage.setEnabled();
  endtask : enableTestEnvironment

  // --------------------------------------------------------------------------
  // Disable test Enviroment
  task disableTestEnvironment();
    int i, busy;

    // Disable drivers
    #(1000*CLK_PERIOD);
    for(int i=0; i<CHANNELS; i++)
      flDriver[i].setDisabled();

    // Check if monitors are not receiving transaction for 100 CLK_PERIODs
    i = 0;
    while (i<100) begin
      busy = 0;
      for (int j=0; j<CHANNELS; j++)
        if (flMonitor[j].busy) busy = 1;
      if (busy) i=0;
      else i++;
      #(CLK_PERIOD);
    end

    // disable Monitor and Responder
    for(int i=0; i<CHANNELS; i++) begin
      flMonitor[i].setDisabled();
      flResponder[i].setDisabled();
    end

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
    for(int i=0; i<CHANNELS; i++) begin
      generator[i].setEnabled(TEST_TRANSACTION_COUNT);
    end

    // wait until all generators are disabled
    for(int i=0; i<CHANNELS; i++) begin
      wait (generator[i].enabled == 0);
    end

    // Disable Test Enviroment
    disableTestEnvironment();

    // Display Scoreboard
    for (int i=0; i<CHANNELS; i++)
      scoreboard[i].display();
    coverage.display();
  endtask: test1

  // --------------------------------------------------------------------------
  // Test Case 2
  // short transactions
  task test2();
    $write("\n\n############ TEST CASE 2 ############\n\n");

    // create & enable environment
    createGeneratorEnvironment(GENERATOR_PACKET_COUNT,'{8, 8, 8},'{1, 1, 1});
    createEnvironment();
    enableTestEnvironment();

    // Run generators
    for(int i=0; i<CHANNELS; i++) begin
      generator[i].setEnabled(TEST_TRANSACTION_COUNT);
    end

    // wait until all generators are disabled
    for(int i=0; i<CHANNELS; i++) begin
      wait (generator[i].enabled == 0);
    end

    // Disable Test Enviroment
    disableTestEnvironment();

    // Display Scoreboard
    for (int i=0; i<CHANNELS; i++)
      scoreboard[i].display();
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
    for(int i=0; i<CHANNELS; i++) begin
      flResponder[i].rxDelayEn_wt        = 0;
      flResponder[i].insideRxDelayEn_wt  = 0;
    end

    // Enable Test environment
    enableTestEnvironment();

    // Run generators
    for(int i=0; i<CHANNELS; i++) begin
      generator[i].setEnabled(TEST_TRANSACTION_COUNT);
    end

    // wait until all generators are disabled
    for(int i=0; i<CHANNELS; i++) begin
      wait (generator[i].enabled == 0);
    end

    // Disable Test Enviroment
    disableTestEnvironment();

    // Display Scoreboard
    for (int i=0; i<CHANNELS; i++)
      scoreboard[i].display();
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
    for(int i=0; i<CHANNELS; i++) begin
      flResponder[i].rxDelayEn_wt            = 5;
      flResponder[i].rxDelayDisable_wt       = 1;
      flResponder[i].rxDelayLow              = 0;
      flResponder[i].rxDelayHigh             = 4;
      flResponder[i].insideRxDelayEn_wt      = 5;
      flResponder[i].insideRxDelayDisable_wt = 1;
      flResponder[i].insideRxDelayLow        = 0;
      flResponder[i].insideRxDelayHigh       = 4;
    end

    // Enable Test environment
    enableTestEnvironment();

    // Run generators
    for(int i=0; i<CHANNELS; i++) begin
      generator[i].setEnabled(TEST_TRANSACTION_COUNT);
    end

    // wait until all generators are disabled
    for(int i=0; i<CHANNELS; i++) begin
      wait (generator[i].enabled == 0);
    end

    // Disable Test Enviroment
    disableTestEnvironment();

    // Display Scoreboard
    for (int i=0; i<CHANNELS; i++)
      scoreboard[i].display();
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

