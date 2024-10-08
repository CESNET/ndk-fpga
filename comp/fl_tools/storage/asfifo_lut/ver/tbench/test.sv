/*
 * test.sv: AS_FIFO automatic test
 * Copyright (C) 2009 CESNET
 * Author(s): Marek Santa <xsanta06@stud.fit.vutbr.cz>
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
import test_pkg::*;

// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
// V PRIPADE POTREBY DOPLNIT FRAMELINKOVE ROZHRANIA
program TEST (
  input  logic     RX_CLK,
  output logic     RX_RESET,
  input  logic     TX_CLK,
  output logic     TX_RESET,
  iFrameLinkRx.tb  RX,
  iFrameLinkTx.tb  TX,
  iFrameLinkTx.monitor MONITOR
  );

  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------

  // AK MA KOMPONENTA VIAC DRIVEROV ALEBO MONITOROV TREBA ICH NA TOMTO MIESTE DEKLAROVAT A V TASKU
  // CREATEENVIRONMENT INSTANCIOVAT

  FrameLinkTransaction                 flBlueprint;                             // Transaction
  Generator                            generator;                               // Generator
  FrameLinkDriver #(DRIVER0_DATA_WIDTH, DRIVER0_DREM_WIDTH)     flDriver;       // Driver
  FrameLinkMonitor #(MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH)  flMonitor;      // Monitor
  FrameLinkResponder #(MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH)  flResponder;  // Responder
  Scoreboard                           scoreboard;                              // Scoreboard
  Coverage #(RX_DATA_WIDTH,RX_DREM_WIDTH,TX_DATA_WIDTH,TX_DREM_WIDTH) coverage; // Coverage

  // --------------------------------------------------------------------------
  //                       Creating Environment tasks
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Create Test Environment
  task createGeneratorEnvironment(int packet_count = GENERATOR0_FL_PACKET_COUNT,
                                  int packet_size_max[] = GENERATOR0_FL_PACKET_SIZE_MAX,
                                  int packet_size_min[] = GENERATOR0_FL_PACKET_SIZE_MIN
                                  );
  // Create generator
    generator = new("Generator0", 0);
      flBlueprint = new;
      flBlueprint.packetCount   = packet_count;
      flBlueprint.packetSizeMax = packet_size_max;
      flBlueprint.packetSizeMin = packet_size_min;
      generator.blueprint       = flBlueprint;
  endtask: createGeneratorEnvironment

  task createEnvironment();
    // Create driver
    flDriver  = new ("Driver0", generator.transMbx, RX);
      flDriver.txDelayEn_wt             = DRIVER0_DELAYEN_WT;
      flDriver.txDelayDisable_wt        = DRIVER0_DELAYDIS_WT;
      flDriver.txDelayLow               = DRIVER0_DELAYLOW;
      flDriver.txDelayHigh              = DRIVER0_DELAYHIGH;
      flDriver.insideTxDelayEn_wt       = DRIVER0_INSIDE_DELAYEN_WT;
      flDriver.insideTxDelayDisable_wt  = DRIVER0_INSIDE_DELAYDIS_WT;
      flDriver.insideTxDelayLow         = DRIVER0_INSIDE_DELAYLOW;
      flDriver.insideTxDelayHigh        = DRIVER0_INSIDE_DELAYHIGH;
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
    coverage = new();
      coverage.addFrameLinkInterfaceRx(RX,"RXcoverage");
      coverage.addFrameLinkInterfaceTx(MONITOR,"TXcoverage");
    // Set Callbacks
    // V PRIPADE VIAC DRIVEROV ALEBO MONITOROV TREBA VOLAT PRISLUSNE CALLBACKS
      flDriver.setCallbacks(scoreboard.driverCbs);
      flMonitor.setCallbacks(scoreboard.monitorCbs);
  endtask : createEnvironment

  // --------------------------------------------------------------------------
  //                       Test auxilarity procedures
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Resets design
  task resetDesign();
    #(2*RX_CLK_PERIOD);               // wait before reset
    RX_RESET=1;                       // Init Reset variable
    TX_RESET=1;                       // Init Reset variable
    #TX_RESET_TIME;
    RX_RESET = 0;     // Deactivate reset after reset_time
    TX_RESET = 0;     // Deactivate reset after reset_time
    #TX_RESET_TIME;
  endtask : resetDesign

  // --------------------------------------------------------------------------
  // Enable test Environment
  task enableTestEnvironment();
    // Enable Driver, Monitor, Coverage for each port
    // V PRIPADE POTREBY ZAPNUT VSETKY POUZITE DRIVERY A MONITORY A RESPONDERY
    flDriver.setEnabled();
    flMonitor.setEnabled();
    flResponder.setEnabled();
    coverage.setEnabled();
  endtask : enableTestEnvironment

  // --------------------------------------------------------------------------
  // Disable test Environment
  task disableTestEnvironment();
     int i;
     #(1000*TX_CLK_PERIOD);
     i = 0;
     // Check if monitor is not receiving transaction for 100 CLK_PERIODs
     while (i<100) begin
        if (flDriver.busy || flMonitor.busy)
           i = 0;
        else
           i++;
        #(TX_CLK_PERIOD);
     end
     flDriver.setDisabled();
     flMonitor.setDisabled();
     flResponder.setDisabled();
     coverage.setDisabled();
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

     // wait until generator is disabled
     wait (generator.enabled == 0);

     // Disable Test Enviroment
     disableTestEnvironment();

     // Display Scoreboard
     scoreboard.display();
     coverage.display();
  endtask: test1

  // --------------------------------------------------------------------------
  // Test Case 2
  // Generuje jednopaketove framy, ktore sa zmestia do jedneho slova driveru
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
     coverage.display();
  endtask: test2

  // --------------------------------------------------------------------------
  // Test Case 3
  // short transactions
  task test3();
    $write("\n\n############ TEST CASE 3 ############\n\n");

    // create & enable environment
    createGeneratorEnvironment(3,'{8, 8, 8},'{1, 1, 1});
    createEnvironment();
    enableTestEnvironment();

    // Run generators
    generator.setEnabled(TRANSACTION_COUNT);

    // wait until generator is disabled
    wait (generator.enabled == 0);

    // Disable Test Enviroment
    disableTestEnvironment();

    // Display Scoreboard
    scoreboard.display();
    coverage.display();
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
    coverage.display();
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
    coverage.display();
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
    $timeformat(-9, 0, "ns", 8);
    $write("\n\n############ GENERICS ############\n\n");
    $write("RX_CLK_PERIOD:%t\nTX_CLK_PERIOD:%t\n",RX_CLK_PERIOD,TX_CLK_PERIOD);

    test1();       // Run Test 1
    resetDesign();

    test2();
    test3();
    test4();
    test5();

    // -------------------------------------
    // STOP TESTING
    // -------------------------------------
    $write("Verification finished successfully!\n");
    $stop();       // Stop testing
  end

endprogram

