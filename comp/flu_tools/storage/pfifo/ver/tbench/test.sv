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
      fluDriver.delayEn_wt             = DRIVER0_DELAYEN_WT;
      fluDriver.delayDisable_wt        = DRIVER0_DELAYDIS_WT;
      fluDriver.delayLow               = DRIVER0_DELAYLOW;
      fluDriver.delayHigh              = DRIVER0_DELAYHIGH;
    fluDriver.setCallbacks(scoreboard.driverCbs);

   // Create and connect monitor and responder
      fluMonitor   = new ("Monitor0", MONITOR);
      fluResponder = new ("Responder0", TX);
         fluResponder.rxDelayEn_wt        = MONITOR0_DELAYEN_WT;
         fluResponder.rxDelayDisable_wt   = MONITOR0_DELAYDIS_WT;
         fluResponder.rxDelayLow          = MONITOR0_DELAYLOW;
         fluResponder.rxDelayHigh         = MONITOR0_DELAYHIGH;
         fluResponder.insideRxDelayEn_wt  = MONITOR0_INSIDE_DELAYEN_WT;
         fluResponder.insideRxDelayDisable_wt=MONITOR0_INSIDE_DELAYDIS_WT;
         fluResponder.insideRxDelayLow    = MONITOR0_INSIDE_DELAYLOW;
         fluResponder.insideRxDelayHigh   = MONITOR0_INSIDE_DELAYHIGH;
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
     #(10000*TX_CLK_PERIOD);
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
  // Generate Normal packets with lot of waiting on RX side, no wait on TX side
  task test3();
     $write("\n\n############ TEST CASE 3 ############\n\n");
     // Create Generator Environment
     createGeneratorEnvironment();
     // Create Test environment
     createEnvironment();

     // Set slow RX side
     fluResponder.rxDelayEn_wt            = 5;
     fluResponder.rxDelayDisable_wt       = 1;
     fluResponder.rxDelayLow              = 0;
     fluResponder.rxDelayHigh             = 10;
     fluResponder.insideRxDelayEn_wt      = 5;
     fluResponder.insideRxDelayDisable_wt = 1;
     fluResponder.insideRxDelayLow        = 0;
     fluResponder.insideRxDelayHigh       = 10;

     // Set no waiting on TX
     fluResponder.rxDelayEn_wt        = 0;
     fluResponder.insideRxDelayEn_wt  = 0;

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
  endtask: test3

  // --------------------------------------------------------------------------
  // Test Case 4
  // Generate Normal packets with no wait on RX side, no wait on TX side
  task test4();
     $write("\n\n############ TEST CASE 4 ############\n\n");
     // Create Generator Environment
     createGeneratorEnvironment();
     // Create Test environment
     createEnvironment();

     // Set slow RX side
     fluDriver.delayEn_wt           = 0;
     fluDriver.insideTxDelayEn_wt   = 0;

     // Set no waiting on TX
     fluResponder.rxDelayEn_wt        = 0;
     fluResponder.insideRxDelayEn_wt  = 0;

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
  endtask: test4

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
    test1();
    test2();
    test3();
    test4();

    // -------------------------------------
    // STOP TESTING
    // -------------------------------------
    $stop();       // Stop testing
  end

endprogram

