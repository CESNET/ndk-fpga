/*
 * test.sv: Automatic test
 * Copyright (C) 2012 CESNET
 * Author(s): Pavel Benacek <benacek@cesnet.cz>
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
   input logic RX_CLK,
   input logic TX_CLK,
   output logic RESET,
   iFrameLinkURx.tb RX,
   iFrameLinkUTx.tb TX,
   iFrameLinkUTx.monitor MONITOR
  );

  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------

  FrameLinkUTransaction                fluBlueprint;                             // Transaction
  Generator                            generator;                               // Generator
  FrameLinkUDriver #(DRIVER0_DATA_WIDTH, DRIVER0_EOP_WIDTH, DRIVER0_SOP_WIDTH)   fluDriver;       // Driver
  FrameLinkUMonitor #(DRIVER0_DATA_WIDTH, DRIVER0_EOP_WIDTH, DRIVER0_SOP_WIDTH)  fluMonitor;     // Monitor
  FrameLinkUResponder #(DRIVER0_DATA_WIDTH, DRIVER0_EOP_WIDTH, DRIVER0_SOP_WIDTH) fluResponder;  // Responder
  Scoreboard                            scoreboard;                              // Scoreboard

  // --------------------------------------------------------------------------
  //                       Creating Environment tasks
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Create Test Environment
  task createGeneratorEnvironment(int packet_size_max = GENERATOR0_FLU_PACKET_SIZE_MAX,
                                  int packet_size_min = GENERATOR0_FLU_PACKET_SIZE_MIN
                                  );
  // Create generator
    generator = new("Generator", 0);
    fluBlueprint = new;
    fluBlueprint.packetSizeMax = packet_size_max;
    fluBlueprint.packetSizeMin = packet_size_min;
    generator.blueprint       = fluBlueprint;
  endtask: createGeneratorEnvironment

  task createEnvironment();
    string driverLabel;
    // Create scoreboard
    scoreboard = new;

    // Create driver
    fluDriver  = new ("Driver", generator.transMbx, RX);
    fluDriver.insideTxDelayEn_wt       = DRIVER0_INSIDE_DELAYEN_WT;
    fluDriver.insideTxDelayDisable_wt  = DRIVER0_INSIDE_DELAYDIS_WT;
    fluDriver.insideTxDelayLow         = DRIVER0_INSIDE_DELAYLOW;
    fluDriver.insideTxDelayHigh        = DRIVER0_INSIDE_DELAYHIGH;
    fluDriver.startPositionLow         = DRIVER0_START_POS_LOW;
    fluDriver.startPositionHigh        = DRIVER0_START_POS_HIGH;
    fluDriver.setCallbacks(scoreboard.driverCbs);

   // Create and connect monitor and responder
      fluMonitor   = new ("Monitor0", MONITOR);
      fluResponder = new ("Responder0", TX);

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
    fluDriver.setEnabled();
    fluMonitor.setEnabled();
    fluResponder.setEnabled();
  endtask : enableTestEnvironment

  // --------------------------------------------------------------------------
  // Disable test Environment
  task disableTestEnvironment();
     int i;
     #(1000*RX_CLK_PERIOD);
     i = 0;
     // Check if monitor is not receiving transaction for 100 CLK_PERIODs
     while (i<100) begin
        if (fluDriver.busy || fluMonitor.busy)
           i = 0;
        else
           i++;
        #(RX_CLK_PERIOD);
     end
     fluDriver.setDisabled();
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
     // Run generator
     generator.setEnabled(TRANSACTION_COUNT);

     // Pokud je generator aktivni nic nedelej
     wait (generator.enabled == 0);

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
     createGeneratorEnvironment(8,1);

     // Create Test environment
     createEnvironment();
     // Enable Test environment
     enableTestEnvironment();

     // Run generators
     generator.setEnabled(TRANSACTION_COUNT);

     // wait until generator is disabled
     wait (generator.enabled == 0);

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
    generator.setEnabled(TRANSACTION_COUNT);

    // wait until generator is disabled
    wait (generator.enabled == 0);

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

    // set delays
    fluResponder.rxDelayEn_wt            = 5;
    fluResponder.rxDelayDisable_wt       = 1;
    fluResponder.rxDelayLow              = 0;
    fluResponder.rxDelayHigh             = 4;
    fluResponder.insideRxDelayEn_wt      = 5;
    fluResponder.insideRxDelayDisable_wt = 1;
    fluResponder.insideRxDelayLow        = 0;
    fluResponder.insideRxDelayHigh       = 4;
    // Enable Test environment
    enableTestEnvironment();

    // Run generators
    generator.setEnabled(TRANSACTION_COUNT);

    // wait until all generators are disabled
    wait (generator.enabled == 0);

    // Disable Test Enviroment
    disableTestEnvironment();

    // Display Scoreboard
    scoreboard.display();
  endtask: test5

  // --------------------------------------------------------------------------
  // Test Case 6
  // Classic length transactions, A lot of waiting, no TX wait
  task test6();
    $write("\n\n############ TEST CASE 6 ############\n\n");

    // create & enable environment
    createGeneratorEnvironment();
    createEnvironment();

    // A lot of waitin on RX
    fluResponder.rxDelayEn_wt            = 5;
    fluResponder.rxDelayDisable_wt       = 1;
    fluResponder.rxDelayLow              = 0;
    fluResponder.rxDelayHigh             = 4;
    fluResponder.insideRxDelayEn_wt      = 5;
    fluResponder.insideRxDelayDisable_wt = 1;
    fluResponder.insideRxDelayLow        = 0;
    fluResponder.insideRxDelayHigh       = 4;

    // No waiting on TX
    fluResponder.rxDelayEn_wt        = 0;
    fluResponder.insideRxDelayEn_wt  = 0;

    // Enable Test environment
    enableTestEnvironment();

    // Run generators
    generator.setEnabled(TRANSACTION_COUNT);

    // wait until generator is disabled
    wait (generator.enabled == 0);

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

