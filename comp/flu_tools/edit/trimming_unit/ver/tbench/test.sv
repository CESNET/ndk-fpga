/*
 * test.sv: Automatic test
 * Copyright (C) 2012 CESNET
 * Author(s): Lukas Kekely <kekely@cesnet.cz>
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

`include "length_driver.sv"






// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
program TEST (
   input logic CLK,
   output logic RESET,
   lengthInterface.tb LENGTH,
   iFrameLinkURx.tb RX,
   iFrameLinkUTx.tb TX,
   iFrameLinkUTx.monitor MONITOR
  );

  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------

  FrameLinkUTransaction                fluBlueprint;                             // Transaction
  FrameLinkUTransaction                lengthBP;
  Generator                            generator;                               // Generator
  Generator                            glength;
  FrameLinkUDriver #(DRIVER0_DATA_WIDTH, DRIVER0_EOP_WIDTH, DRIVER0_SOP_WIDTH)   fluDriver;       // Driver
  lengthDriver       #(LENGTH_WIDTH) lDriver;
  FrameLinkUMonitor #(DRIVER0_DATA_WIDTH, DRIVER0_EOP_WIDTH, DRIVER0_SOP_WIDTH)  fluMonitor;     // Monitor
  FrameLinkUResponder #(DRIVER0_DATA_WIDTH, DRIVER0_EOP_WIDTH, DRIVER0_SOP_WIDTH) fluResponder;  // Responder
  Scoreboard                           #(LENGTH_WIDTH) scoreboard;                              // Scoreboard

  // --------------------------------------------------------------------------
  //                       Creating Environment tasks
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Create Test Environment
  task createGeneratorEnvironment(int width = LENGTH_WIDTH,
                                  int packet_size_max = GENERATOR0_FLU_PACKET_SIZE_MAX,
                                  int packet_size_min = GENERATOR0_FLU_PACKET_SIZE_MIN
                                  );
  // Create generator
    generator = new("Generator0", 0);
      fluBlueprint = new;
      fluBlueprint.packetSizeMax = packet_size_max;
      fluBlueprint.packetSizeMin = packet_size_min;
      generator.blueprint       = fluBlueprint;
    glength = new("GeneratorI", 1);
      lengthBP = new;
      lengthBP.packetSizeMax = width/8 +1+5; // extra +1 for better chance of all zeros/all ones
      lengthBP.packetSizeMin = width/8 +1+5;
      glength.blueprint = lengthBP;
  endtask: createGeneratorEnvironment

  task createEnvironment();

    // Create driver
    fluDriver  = new ("Driver0", generator.transMbx, RX);
      fluDriver.insideTxDelayEn_wt       = DRIVER0_INSIDE_DELAYEN_WT;
      fluDriver.insideTxDelayDisable_wt  = DRIVER0_INSIDE_DELAYDIS_WT;
      fluDriver.insideTxDelayLow         = DRIVER0_INSIDE_DELAYLOW;
      fluDriver.insideTxDelayHigh        = DRIVER0_INSIDE_DELAYHIGH;
      fluDriver.startPositionLow         = DRIVER0_START_POS_LOW;
      fluDriver.startPositionHigh        = DRIVER0_START_POS_HIGH;
    lDriver = new ("DriverL", glength.transMbx, LENGTH);
      lDriver.DelayEn_wt = DRIVERL_DELAYEN_WT;
      lDriver.DelayDisable_wt = DRIVERL_DELAYDIS_WT;
      lDriver.DelayLow = DRIVERL_DELAYLOW;
      lDriver.DelayHigh = DRIVERL_DELAYHIGH;

   // Create scoreboard
    scoreboard = new;
    fluDriver.setCallbacks(scoreboard.driverCbs);
    lDriver.setCallbacks(scoreboard.driverCbs);

   // Create and connect monitor and responder
    fluMonitor   = new ("Monitor 0", MONITOR);
    fluResponder = new ("Responder 0", TX);
    fluResponder.rxDelayEn_wt            = MONITOR0_DELAYEN_WT;
    fluResponder.rxDelayDisable_wt       = MONITOR0_DELAYDIS_WT;
    fluResponder.rxDelayLow              = MONITOR0_DELAYLOW;
    fluResponder.rxDelayHigh             = MONITOR0_DELAYHIGH;
    fluResponder.insideRxDelayEn_wt      = MONITOR0_INSIDE_DELAYEN_WT;
    fluResponder.insideRxDelayDisable_wt = MONITOR0_INSIDE_DELAYDIS_WT;
    fluResponder.insideRxDelayLow        = MONITOR0_INSIDE_DELAYLOW;
    fluResponder.insideRxDelayHigh       = MONITOR0_INSIDE_DELAYHIGH;
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
    lDriver.setEnabled();
    fluDriver.setEnabled();
    fluMonitor.setEnabled();
    fluResponder.setEnabled();
  endtask : enableTestEnvironment

  // --------------------------------------------------------------------------
  // Disable test Environment
  task disableTestEnvironment();
     #(1000*CLK_PERIOD);
     fluDriver.setDisabled();
     lDriver.setDisabled();
     // Disable monitors
     fluMonitor.setDisabled();
     fluResponder.setDisabled();
  endtask : disableTestEnvironment

  // --------------------------------------------------------------------------
  //                            Test cases
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Test Case 1
  task test1();
     $write("\n\n############ TEST CASE 1 ############\n\n");
     // Enable Test environment
     enableTestEnvironment();
     // Run generators
     glength.setEnabled(TRANSACTION_COUNT);
     generator.setEnabled(TRANSACTION_COUNT);

     // Pokud je generator aktivni nic nedelej
     while (generator.enabled) begin
       #(CLK_PERIOD);
     end

     // Disable Test Enviroment
     disableTestEnvironment();

     // Display Scoreboard
     scoreboard.display();
  endtask: test1

  // --------------------------------------------------------------------------
  // Test Case 2
  // Generate very short packets
  task test2();
     $write("\n\n############ TEST CASE 2 ############\n\n");
     // Create Generator Environment
     createGeneratorEnvironment(LENGTH_WIDTH,8,1);

     // Create Test environment
     createEnvironment();
     // Enable Test environment
     enableTestEnvironment();

     // Run generators
     glength.setEnabled(TRANSACTION_COUNT);
     generator.setEnabled(TRANSACTION_COUNT);

     // wait until generator is disabled
     while (generator.enabled) begin
       #(CLK_PERIOD);
     end

     // Disable Test Environment
     disableTestEnvironment();
     // Display Scoreboard
     scoreboard.display();
  endtask: test2

  // --------------------------------------------------------------------------
  // Test Case 3
  // Classic length transactions, slow TX and fast RX
  task test3();
    $write("\n\n############ TEST CASE 3 ############\n\n");

    // create & enable environment
    createGeneratorEnvironment();
    createEnvironment();

    // set delays
    fluResponder.rxDelayEn_wt            = 5;
    fluResponder.rxDelayDisable_wt       = 1;
    fluResponder.rxDelayLow              = 0;
    fluResponder.rxDelayHigh             = 10;
    fluResponder.insideRxDelayEn_wt      = 5;
    fluResponder.insideRxDelayDisable_wt = 1;
    fluResponder.insideRxDelayLow        = 0;
    fluResponder.insideRxDelayHigh       = 10;

    fluDriver.insideTxDelayEn_wt =0;

    // Enable Test environment
    enableTestEnvironment();

    // Run generators
    glength.setEnabled(TRANSACTION_COUNT);
    generator.setEnabled(TRANSACTION_COUNT);


    // wait until all generators are disabled
    wait (generator.enabled == 0);

    // Disable Test Enviroment
    disableTestEnvironment();

    // Display Scoreboard
    scoreboard.display();
  endtask: test3

  // --------------------------------------------------------------------------
  // Test Case 4
  // Classic length transactions, no TX wait
  task test4();
    $write("\n\n############ TEST CASE 4 ############\n\n");

    // create & enable environment
    createGeneratorEnvironment();
    createEnvironment();

    // set zero delays
    fluResponder.rxDelayEn_wt        = 0;
    fluResponder.insideRxDelayEn_wt  = 0;

    // Enable Test environment
    enableTestEnvironment();

    // Run generators
    glength.setEnabled(TRANSACTION_COUNT);
    generator.setEnabled(TRANSACTION_COUNT);

    // wait until generator is disabled
    while (generator.enabled) begin
       #(CLK_PERIOD);
     end

     // Disable Test Enviroment
    disableTestEnvironment();

    // Display Scoreboard
    scoreboard.display();
  endtask: test4

  // --------------------------------------------------------------------------
  // Test Case 5
  // Classic length transactions, lot of waiting
  task test5();
    $write("\n\n############ TEST CASE 5 ############\n\n");

    // create & enable environment
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
    fluDriver.insideTxDelayEn_wt       = 5;
    fluDriver.insideTxDelayDisable_wt  = 1;
    fluDriver.insideTxDelayLow         = 0;
    fluDriver.insideTxDelayHigh        = 4;

    // Enable Test environment
    enableTestEnvironment();

    // Run generators
    glength.setEnabled(TRANSACTION_COUNT);
    generator.setEnabled(TRANSACTION_COUNT);

    // wait until all generators are disabled
    while (generator.enabled) begin
       #(CLK_PERIOD);
     end

    // Disable Test Enviroment
    disableTestEnvironment();

    // Display Scoreboard
    scoreboard.display();
  endtask: test5

    // --------------------------------------------------------------------------
  // Test Case 6
  // Classic length transactions, fast RX and TX, slow Control
  task test6();
    $write("\n\n############ TEST CASE 6 ############\n\n");

    // create & enable environment
    createGeneratorEnvironment();
    createEnvironment();

    // set delays
    fluResponder.rxDelayEn_wt            = 1;
    fluResponder.rxDelayDisable_wt       = 1;
    fluResponder.rxDelayLow              = 0;
    fluResponder.rxDelayHigh             = 1;
    fluResponder.insideRxDelayEn_wt      = 1;
    fluResponder.insideRxDelayDisable_wt = 1;
    fluResponder.insideRxDelayLow        = 0;
    fluResponder.insideRxDelayHigh       = 1;

    fluDriver.insideTxDelayEn_wt =0;
    lDriver.DelayEn_wt = 5;
    lDriver.DelayDisable_wt = 1;
    lDriver.DelayLow = 5;
    lDriver.DelayHigh = 10;

    // Enable Test environment
    enableTestEnvironment();

    // Run generators
    glength.setEnabled(TRANSACTION_COUNT);
    generator.setEnabled(TRANSACTION_COUNT);

    // wait until all generators are disabled
    while (generator.enabled) begin
       #(CLK_PERIOD);
     end

    // Disable Test Enviroment
    disableTestEnvironment();

    // Display Scoreboard
    scoreboard.display();
  endtask: test6


  // --------------------------------------------------------------------------
  //                           Main test part
  // --------------------------------------------------------------------------
  initial begin
    // -------------------------------------
    // DESIGN ENVIROMENT
    // -------------------------------------
    resetDesign(); // Reset design
    createGeneratorEnvironment();
    createEnvironment(); // Create Test Enviroment
    // -------------------------------------
    // TESTING
    // -------------------------------------
    test1();       // Run Test 1

    test2();
    test3();
    test4();
    test5();
    test6();

    // -------------------------------------
    // STOP TESTING
    // -------------------------------------
    $stop();       // Stop testing
  end

endprogram

