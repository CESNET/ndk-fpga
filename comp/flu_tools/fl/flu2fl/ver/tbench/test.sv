/*
 * test.sv: IB_SWITCH automatic test
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
import sv_fl_pkg::*;
import sv_flu_pkg::*;
import test_pkg::*;

// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
// V PRIPADE POTREBY DOPLNIT FRAMELINKOVE ROZHRANIA
program TEST (
  input  logic     CLK,
  output logic     RESET,
  iFrameLinkURx.tb  RX,
  iFrameLinkTx.tb  TX,
  iFrameLinkTx.monitor MONITOR
  );

  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------

  // AK MA KOMPONENTA VIAC DRIVEROV ALEBO MONITOROV TREBA ICH NA TOMTO MIESTE DEKLAROVAT A V TASKU
  // CREATEENVIRONMENT INSTANCIOVAT

  FrameLinkUTransaction                 fluBlueprint;                             // Transaction
  Generator                            generator;                               // Generator
  FrameLinkUDriver #(DRIVER0_DATA_WIDTH, DRIVER0_EOP_WIDTH, DRIVER0_SOP_WIDTH)     fluDriver;       // Driver
  FrameLinkMonitor #(MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH)  flMonitor;      // Monitor
  FrameLinkResponder #(MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH)  flResponder;  // Responder
  Scoreboard                           scoreboard;                              // Scoreboard
  // Coverage #(RX_DATA_WIDTH,RX_DREM_WIDTH,TX_DATA_WIDTH,TX_DREM_WIDTH) coverage; // Coverage

  // --------------------------------------------------------------------------
  //                       Creating Environment tasks
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Create Test Environment
  task createGeneratorEnvironment(int packet_count = GENERATOR0_FL_PACKET_COUNT,
                                  int packet_size_max = GENERATOR0_FL_PACKET_SIZE_MAX,
                                  int packet_size_min = GENERATOR0_FL_PACKET_SIZE_MIN
                                  );
  // Create generator
    generator = new("Generator0", 0);
      fluBlueprint = new;
      fluBlueprint.packetSizeMax = packet_size_max;
      fluBlueprint.packetSizeMin = packet_size_min;
      generator.blueprint       = fluBlueprint;
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

    // Create monitor
    flMonitor = new ("Monitor0", MONITOR);
    // Create responder
    flResponder = new ("Responder0", TX);
      flResponder.rxDelayEn_wt            = MONITOR0_DELAYEN_WT;
      flResponder.rxDelayDisable_wt       = MONITOR0_DELAYDIS_WT;
      flResponder.rxDelayLow              = MONITOR0_DELAYLOW;
      flResponder.rxDelayHigh             = MONITOR0_DELAYHIGH;
      flResponder.insideRxDelayEn_wt      = MONITOR0_INSIDE_DELAYEN_WT;
      flResponder.insideRxDelayDisable_wt = MONITOR0_INSIDE_DELAYDIS_WT;
      flResponder.insideRxDelayLow        = MONITOR0_INSIDE_DELAYLOW;
      flResponder.insideRxDelayHigh       = MONITOR0_INSIDE_DELAYHIGH;
    // Create scoreboard
    scoreboard = new;
    // Coverage class
    // V PRIPADE VIAC INTERFACOV TREBA VOLAT PRISLUSNY COVERAGE PODLA TYPU INTERFACE
    //coverage = new();
     // coverage.addFrameLinkInterfaceRx(RX,"RXcoverage");
     // coverage.addFrameLinkInterfaceTx(MONITOR,"TXcoverage");
    // Set Callbacks
    // V PRIPADE VIAC DRIVEROV ALEBO MONITOROV TREBA VOLAT PRISLUSNE CALLBACKS
      fluDriver.setCallbacks(scoreboard.driverCbs);
      flMonitor.setCallbacks(scoreboard.monitorCbs);
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
    // Enable Driver, Monitor, Coverage for each port
    // V PRIPADE POTREBY ZAPNUT VSETKY POUZITE DRIVERY A MONITORY A RESPONDERY
    fluDriver.setEnabled();
    flMonitor.setEnabled();
    flResponder.setEnabled();
    //coverage.setEnabled();
  endtask : enableTestEnvironment

  // --------------------------------------------------------------------------
  // Disable test Environment
  task disableTestEnvironment();
     // V PRIPADE POTREBY VYPNUT VSETKY POUZITE DRIVERY A MONITORY A RESPONDERY
     // Disable drivers
     #(1000*CLK_PERIOD);
     fluDriver.setDisabled();
     // Disable monitors
     flMonitor.setDisabled();
     flResponder.setDisabled();
     //coverage.setDisabled();
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
     generator.setEnabled(TRANSACTION_COUNT);

     // Pokud je generator aktivni nic nedelej
     while (generator.enabled)
       #(CLK_PERIOD);

     // Disable Test Enviroment
     disableTestEnvironment();

     // Display Scoreboard
     scoreboard.display();
     //coverage.display();
  endtask: test1

  // --------------------------------------------------------------------------
  // Test Case 2
  // Generate very short packets
  task test2();
     $write("\n\n############ TEST CASE 2 ############\n\n");
     // Create Generator Environment
     createGeneratorEnvironment(1,'{8},'{1});

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
     //coverage.display();
  endtask: test2

  // --------------------------------------------------------------------------
  // Test Case 4
  // Classic length transactions, no TX wait
  task test4();
    $write("\n\n############ TEST CASE 4 ############\n\n");

    // create & enable environment
    createGeneratorEnvironment();
    createEnvironment();

    // set zero delays
    flResponder.rxDelayEn_wt        = 0;
    flResponder.insideRxDelayEn_wt  = 0;

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
    //coverage.display();
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
    generator.setEnabled(TRANSACTION_COUNT);

    // wait until all generators are disabled
    wait (generator.enabled == 0);

    // Disable Test Enviroment
    disableTestEnvironment();

    // Display Scoreboard
    scoreboard.display();
    //coverage.display();
  endtask: test5

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
    resetDesign();

    test2();
    //test3();
    test4();
    test5();
    $write("Verification finished successfully!\n");

    // -------------------------------------
    // STOP TESTING
    // -------------------------------------
    $stop();       // Stop testing
  end

endprogram

