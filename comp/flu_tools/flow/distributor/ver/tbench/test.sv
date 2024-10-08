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

`include "inum_driver.sv"






// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
program TEST (
   input logic CLK,
   output logic RESET,
   inumInterface.tb INUM,
   iFrameLinkURx.tb RX,
   iFrameLinkUTx.tb TX[PORTS],
   iFrameLinkUTx.monitor MONITOR[PORTS]
  );

  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------

  FrameLinkUTransaction                fluBlueprint;                             // Transaction
  FrameLinkUTransaction                inumBP;
  Generator                            generator;                               // Generator
  Generator                            ginum;
  FrameLinkUDriver #(DRIVER0_DATA_WIDTH, DRIVER0_EOP_WIDTH, DRIVER0_SOP_WIDTH)   fluDriver;       // Driver
  inumDriver       #(PORTS) iDriver;
  FrameLinkUMonitor #(DRIVER0_DATA_WIDTH, DRIVER0_EOP_WIDTH, DRIVER0_SOP_WIDTH)  fluMonitor[PORTS];     // Monitor
  FrameLinkUResponder #(DRIVER0_DATA_WIDTH, DRIVER0_EOP_WIDTH, DRIVER0_SOP_WIDTH) fluResponder[PORTS];  // Responder
  Scoreboard                           #(PORTS) scoreboard;                              // Scoreboard

  virtual iFrameLinkUTx.tb      #(DRIVER0_DATA_WIDTH, DRIVER0_EOP_WIDTH, DRIVER0_SOP_WIDTH) vTX[PORTS];
  virtual iFrameLinkUTx.monitor #(DRIVER0_DATA_WIDTH, DRIVER0_EOP_WIDTH, DRIVER0_SOP_WIDTH) vMONITOR[PORTS];

  // --------------------------------------------------------------------------
  //                       Creating Environment tasks
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Create Test Environment
  task createGeneratorEnvironment(int ports = PORTS,
                                  int packet_size_max = GENERATOR0_FLU_PACKET_SIZE_MAX,
                                  int packet_size_min = GENERATOR0_FLU_PACKET_SIZE_MIN
                                  );
  // Create generator
    generator = new("Generator0", 0);
      fluBlueprint = new;
      fluBlueprint.packetSizeMax = packet_size_max;
      fluBlueprint.packetSizeMin = packet_size_min;
      generator.blueprint       = fluBlueprint;
    ginum = new("GeneratorI", 1);
      inumBP = new;
      inumBP.packetSizeMax = ports/8 +1;
      inumBP.packetSizeMin = ports/8 +1;
      ginum.blueprint = inumBP;
  endtask: createGeneratorEnvironment

  task createEnvironment();
    vTX      = TX;
    vMONITOR = MONITOR;

    // Create driver
    fluDriver  = new ("Driver0", generator.transMbx, RX);
      fluDriver.insideTxDelayEn_wt       = DRIVER0_INSIDE_DELAYEN_WT;
      fluDriver.insideTxDelayDisable_wt  = DRIVER0_INSIDE_DELAYDIS_WT;
      fluDriver.insideTxDelayLow         = DRIVER0_INSIDE_DELAYLOW;
      fluDriver.insideTxDelayHigh        = DRIVER0_INSIDE_DELAYHIGH;
      fluDriver.startPositionLow         = DRIVER0_START_POS_LOW;
      fluDriver.startPositionHigh        = DRIVER0_START_POS_HIGH;
    iDriver = new ("DriverI", ginum.transMbx, INUM);
      iDriver.DelayEn_wt = DRIVERI_DELAYEN_WT;
      iDriver.DelayDisable_wt = DRIVERI_DELAYDIS_WT;
      iDriver.DelayLow = DRIVERI_DELAYLOW;
      iDriver.DelayHigh = DRIVERI_DELAYHIGH;

   // Create scoreboard
    scoreboard = new;
    fluDriver.setCallbacks(scoreboard.driverCbs);
    iDriver.setCallbacks(scoreboard.driverCbs);

   // Create and connect monitor and responder
    for(int i=0; i<PORTS; i++) begin
      string monitorLabel;
      string responderLabel;

      monitorLabel = $sformatf( "Monitor %0d", i);
      responderLabel = $sformatf( "Responder %0d", i);
      fluMonitor[i]   = new (monitorLabel, vMONITOR[i]);
      fluResponder[i] = new (responderLabel, vTX[i]);

      fluResponder[i].rxDelayEn_wt            = MONITOR0_DELAYEN_WT;
      fluResponder[i].rxDelayDisable_wt       = MONITOR0_DELAYDIS_WT;
      fluResponder[i].rxDelayLow              = MONITOR0_DELAYLOW;
      fluResponder[i].rxDelayHigh             = MONITOR0_DELAYHIGH;
      fluResponder[i].insideRxDelayEn_wt      = MONITOR0_INSIDE_DELAYEN_WT;
      fluResponder[i].insideRxDelayDisable_wt = MONITOR0_INSIDE_DELAYDIS_WT;
      fluResponder[i].insideRxDelayLow        = MONITOR0_INSIDE_DELAYLOW;
      fluResponder[i].insideRxDelayHigh       = MONITOR0_INSIDE_DELAYHIGH;
      fluMonitor[i].setCallbacks(scoreboard.monitorCbs);
    end;

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
    iDriver.setEnabled();
    fluDriver.setEnabled();
    for(int i=0; i<PORTS; i++) begin
    fluMonitor[i].setEnabled();
    fluResponder[i].setEnabled();
    end;
  endtask : enableTestEnvironment

  // --------------------------------------------------------------------------
  // Disable test Environment
  task disableTestEnvironment();
     #(1000*CLK_PERIOD);
     fluDriver.setDisabled();
     iDriver.setDisabled();
     // Disable monitors
     for(int i=0; i<PORTS; i++) begin
     fluMonitor[i].setDisabled();
     fluResponder[i].setDisabled();
     end;
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
     ginum.setEnabled(TRANSACTION_COUNT);
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
     createGeneratorEnvironment(PORTS,8,1);

     // Create Test environment
     createEnvironment();
     // Enable Test environment
     enableTestEnvironment();

     // Run generators
     ginum.setEnabled(TRANSACTION_COUNT);
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
  // Classic length transactions, slow TX and fast RX  (full fifo)
  task test3();
    $write("\n\n############ TEST CASE 3 ############\n\n");

    // create & enable environment
    createGeneratorEnvironment();
    createEnvironment();

    // set delays
    for(int i=0; i<PORTS; i++) begin
    fluResponder[i].rxDelayEn_wt            = 5;
    fluResponder[i].rxDelayDisable_wt       = 1;
    fluResponder[i].rxDelayLow              = 0;
    fluResponder[i].rxDelayHigh             = 10;
    fluResponder[i].insideRxDelayEn_wt      = 5;
    fluResponder[i].insideRxDelayDisable_wt = 1;
    fluResponder[i].insideRxDelayLow        = 0;
    fluResponder[i].insideRxDelayHigh       = 10;
    end

    fluDriver.insideTxDelayEn_wt =0;

    // Enable Test environment
    enableTestEnvironment();

    // Run generators
    ginum.setEnabled(TRANSACTION_COUNT);
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
    for(int i=0; i<PORTS; i++) begin
    fluResponder[i].rxDelayEn_wt        = 0;
    fluResponder[i].insideRxDelayEn_wt  = 0;
    end

    // Enable Test environment
    enableTestEnvironment();

    // Run generators
    ginum.setEnabled(TRANSACTION_COUNT);
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

    // set delays
    for(int i=0; i<PORTS; i++) begin
    fluResponder[i].rxDelayEn_wt            = 5;
    fluResponder[i].rxDelayDisable_wt       = 1;
    fluResponder[i].rxDelayLow              = 0;
    fluResponder[i].rxDelayHigh             = 4;
    fluResponder[i].insideRxDelayEn_wt      = 5;
    fluResponder[i].insideRxDelayDisable_wt = 1;
    fluResponder[i].insideRxDelayLow        = 0;
    fluResponder[i].insideRxDelayHigh       = 4;
    end
    // Enable Test environment
    enableTestEnvironment();

    // Run generators
    ginum.setEnabled(TRANSACTION_COUNT);
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
  // Classic length transactions, fast RX and TX0, slow other TXs
  task test6();
    $write("\n\n############ TEST CASE 6 ############\n\n");

    // create & enable environment
    createGeneratorEnvironment();
    createEnvironment();

    // set delays
    fluResponder[0].rxDelayEn_wt            = 1;
    fluResponder[0].rxDelayDisable_wt       = 1;
    fluResponder[0].rxDelayLow              = 0;
    fluResponder[0].rxDelayHigh             = 1;
    fluResponder[0].insideRxDelayEn_wt      = 1;
    fluResponder[0].insideRxDelayDisable_wt = 1;
    fluResponder[0].insideRxDelayLow        = 0;
    fluResponder[0].insideRxDelayHigh       = 1;
    for(int i=1; i<PORTS; i++) begin
    fluResponder[i].rxDelayEn_wt            = 5;
    fluResponder[i].rxDelayDisable_wt       = 1;
    fluResponder[i].rxDelayLow              = 0;
    fluResponder[i].rxDelayHigh             = 10;
    fluResponder[i].insideRxDelayEn_wt      = 5;
    fluResponder[i].insideRxDelayDisable_wt = 1;
    fluResponder[i].insideRxDelayLow        = 0;
    fluResponder[i].insideRxDelayHigh       = 10;
    end

    fluDriver.insideTxDelayEn_wt =0;

    // Enable Test environment
    enableTestEnvironment();

    // Run generators
    ginum.setEnabled(TRANSACTION_COUNT);
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
    $write("Verification finished successfully!\n");

    // -------------------------------------
    // STOP TESTING
    // -------------------------------------
    $stop();       // Stop testing
  end

endprogram

