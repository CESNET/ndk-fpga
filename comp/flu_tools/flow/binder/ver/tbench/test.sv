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






// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
program TEST (
   input logic CLK,
   output logic RESET,
   iFrameLinkURx.tb RX[PORTS],
   iFrameLinkUTx.tb TX,
   iFrameLinkUTx.monitor MONITOR
  );

  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------

  FrameLinkUTransaction                fluBlueprint[PORTS];                             // Transaction
  Generator                            generator[PORTS];                               // Generator
  FrameLinkUDriver #(DRIVER0_DATA_WIDTH, DRIVER0_EOP_WIDTH, DRIVER0_SOP_WIDTH)   fluDriver[PORTS];       // Driver
  FrameLinkUMonitor #(DRIVER0_DATA_WIDTH, DRIVER0_EOP_WIDTH, DRIVER0_SOP_WIDTH)  fluMonitor;     // Monitor
  FrameLinkUResponder #(DRIVER0_DATA_WIDTH, DRIVER0_EOP_WIDTH, DRIVER0_SOP_WIDTH) fluResponder;  // Responder
  Scoreboard                            scoreboard;                              // Scoreboard

   virtual iFrameLinkURx.tb      #(DRIVER0_DATA_WIDTH, DRIVER0_EOP_WIDTH, DRIVER0_SOP_WIDTH) vRX[PORTS];

  // --------------------------------------------------------------------------
  //                       Creating Environment tasks
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Create Test Environment
  task createGeneratorEnvironment(int packet_size_max = GENERATOR0_FLU_PACKET_SIZE_MAX,
                                  int packet_size_min = GENERATOR0_FLU_PACKET_SIZE_MIN
                                  );
  // Create generator
    for (int i=0; i<PORTS; i++) begin
    generator[i] = new("Generator", i);
      fluBlueprint[i] = new;
      fluBlueprint[i].packetSizeMax = packet_size_max;
      fluBlueprint[i].packetSizeMin = packet_size_min;
      generator[i].blueprint       = fluBlueprint[i];
    end;
  endtask: createGeneratorEnvironment

  task createEnvironment();
    string driverLabel;
    vRX=RX;
    // Create scoreboard
    scoreboard = new;

    // Create driver
    for (int i=0; i<PORTS; i++) begin

    driverLabel = $sformatf( "Driver %0d", i);
    fluDriver[i]  = new (driverLabel, generator[i].transMbx, vRX[i]);
      fluDriver[i].insideTxDelayEn_wt       = DRIVER0_INSIDE_DELAYEN_WT;
      fluDriver[i].insideTxDelayDisable_wt  = DRIVER0_INSIDE_DELAYDIS_WT;
      fluDriver[i].insideTxDelayLow         = DRIVER0_INSIDE_DELAYLOW;
      fluDriver[i].insideTxDelayHigh        = DRIVER0_INSIDE_DELAYHIGH;
      fluDriver[i].startPositionLow         = DRIVER0_START_POS_LOW;
      fluDriver[i].startPositionHigh        = DRIVER0_START_POS_HIGH;
    fluDriver[i].setCallbacks(scoreboard.driverCbs);
    end;

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
    for(int i=0; i<PORTS; i++) fluDriver[i].setEnabled();
    fluMonitor.setEnabled();
    fluResponder.setEnabled();
  endtask : enableTestEnvironment

  // --------------------------------------------------------------------------
  // Disable test Environment
  task disableTestEnvironment();
     #(1000*CLK_PERIOD);
     for(int i=0; i<PORTS; i++) fluDriver[i].setDisabled();
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
     for(int i=0; i<PORTS; i++) generator[i].setEnabled(TRANSACTION_COUNT);

     // Pokud je generator aktivni nic nedelej
     for(int i=0; i<PORTS; i++) wait (generator[i].enabled == 0);

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
     for(int i=0; i<PORTS; i++) generator[i].setEnabled(TRANSACTION_COUNT);

     // wait until generator is disabled
     for(int i=0; i<PORTS; i++) wait (generator[i].enabled == 0);

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

    for(int i=0; i<PORTS; i++)
    fluDriver[i].insideTxDelayEn_wt =0;

    // Enable Test environment
    enableTestEnvironment();

    // Run generators
    for(int i=0; i<PORTS; i++) generator[i].setEnabled(TRANSACTION_COUNT);

    // wait until all generators are disabled
    for(int i=0; i<PORTS; i++)
      wait (generator[i].enabled == 0);

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
    for(int i=0; i<PORTS; i++) generator[i].setEnabled(TRANSACTION_COUNT);

    // wait until generator is disabled
    for(int i=0; i<PORTS; i++) wait (generator[i].enabled == 0);

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
    for(int i=0; i<PORTS; i++) generator[i].setEnabled(TRANSACTION_COUNT);

    // wait until all generators are disabled
    for(int i=0; i<PORTS; i++) wait (generator[i].enabled == 0);

    // Disable Test Enviroment
    disableTestEnvironment();

    // Display Scoreboard
    scoreboard.display();
  endtask: test5

    // --------------------------------------------------------------------------
  // Test Case 6
  // Classic length transactions, fast RX0 and TX, slow other RXs
  task test6();
    $write("\n\n############ TEST CASE 6 ############\n\n");

    // create & enable environment
    createGeneratorEnvironment();
    createEnvironment();

    // set delays
    fluDriver[0].insideTxDelayEn_wt      = 1;
    fluDriver[0].insideTxDelayDisable_wt = 1;
    fluDriver[0].insideTxDelayLow        = 0;
    fluDriver[0].insideTxDelayHigh       = 1;
    for(int i=1; i<PORTS; i++) begin
    fluDriver[i].insideTxDelayEn_wt      = 5;
    fluDriver[i].insideTxDelayDisable_wt = 1;
    fluDriver[i].insideTxDelayLow        = 0;
    fluDriver[i].insideTxDelayHigh       = 10;
    end

    fluResponder.insideRxDelayEn_wt =0;
    fluResponder.rxDelayEn_wt =0;

    // Enable Test environment
    enableTestEnvironment();

    // Run generators
    for(int i=0; i<PORTS; i++) generator[i].setEnabled(TRANSACTION_COUNT);

    // wait until all generators are disabled
    for(int i=0; i<PORTS; i++) wait (generator[i].enabled == 0);

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
    $write("Verification finished successfully!\n");

    // -------------------------------------
    // STOP TESTING
    // -------------------------------------
    $stop();       // Stop testing
  end

endprogram

