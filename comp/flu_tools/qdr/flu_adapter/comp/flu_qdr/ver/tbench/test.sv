/*
 * test.sv: FLU_QDR automatic test
 * Copyright (C) 2014 CESNET
 * Author: Vaclav Hummel <xhumme00@stud.fit.vutbr.cz>
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
// V PRIPADE POTREBY DOPLNIT FRAMELINKOVE ROZHRANIA
program TEST (
  input  logic         APP_CLK,
  output logic         APP_RST,
  input  logic         QDR_CLK,
  output logic         QDR_RST,
  iFrameLinkURx.tb      RX,
  iFrameLinkUTx.tb      TX,
  iFrameLinkUTx.monitor MONITOR
  );

  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------

  // AK MA KOMPONENTA VIAC DRIVEROV ALEBO MONITOROV TREBA ICH NA TOMTO
  // MIESTE DEKLAROVAT A V TASKU CREATEENVIRONMENT INSTANCIOVAT

  // Transaction
  FrameLinkUTransaction    fluBlueprint;

  // Generator
  Generator               generator;

  // Driver
  FrameLinkUDriver #(DRIVER0_DATA_WIDTH, DRIVER0_EOP_WIDTH, DRIVER0_SOP_WIDTH)       fluDriver;

  // Monitor
  FrameLinkUMonitor #(DRIVER0_DATA_WIDTH, DRIVER0_EOP_WIDTH, DRIVER0_SOP_WIDTH)    fluMonitor;

  // Responder
  FrameLinkUResponder #(DRIVER0_DATA_WIDTH, DRIVER0_EOP_WIDTH, DRIVER0_SOP_WIDTH)  fluResponder;

  // Scoreboard
  Scoreboard              scoreboard;

  // Coverage
  //Coverage #(DATA_WIDTH,DREM_WIDTH,DATA_WIDTH,DREM_WIDTH)         coverage;
  //FifoCoverage #(STATUS_WIDTH)                                    fifoCoverage;

  // --------------------------------------------------------------------------
  //                       Creating Environment tasks
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Create Generator Environment
  task createGeneratorEnvironment(int packet_size_max = GENERATOR0_FLU_PACKET_SIZE_MAX,
                                  int packet_size_min = GENERATOR0_FLU_PACKET_SIZE_MIN
                                  );
  // Create generator
    generator = new("Generator0", 0);
      fluBlueprint = new;
      fluBlueprint.packetSizeMax = packet_size_max;
      fluBlueprint.packetSizeMin = packet_size_min;
      generator.blueprint       = fluBlueprint;
  endtask: createGeneratorEnvironment

  // Create Test Environment
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
    fluMonitor = new ("Monitor0", MONITOR);
    // Create responder
    fluResponder = new ("Responder0", TX);
      fluResponder.rxDelayEn_wt            = MONITOR0_DELAYEN_WT;
      fluResponder.rxDelayDisable_wt       = MONITOR0_DELAYDIS_WT;
      fluResponder.rxDelayLow              = MONITOR0_DELAYLOW;
      fluResponder.rxDelayHigh             = MONITOR0_DELAYHIGH;
      fluResponder.insideRxDelayEn_wt      = MONITOR0_INSIDE_DELAYEN_WT;
      fluResponder.insideRxDelayDisable_wt = MONITOR0_INSIDE_DELAYDIS_WT;
      fluResponder.insideRxDelayLow        = MONITOR0_INSIDE_DELAYLOW;
      fluResponder.insideRxDelayHigh       = MONITOR0_INSIDE_DELAYHIGH;

    // Create scoreboard
    scoreboard = new;
    // Coverage class
    //coverage = new();
    //  coverage.addFrameLinkInterfaceRx(RX,"RXcoverage");
    //  coverage.addFrameLinkInterfaceTx(MONITOR,"TXcoverage");
    //fifoCoverage = new();
    //  fifoCoverage.addFrameLinkInterfaceFifo(CTRL,"CTRLcoverage");
    // Set Callbacks
      fluDriver.setCallbacks(scoreboard.driverCbs);
      fluMonitor.setCallbacks(scoreboard.monitorCbs);
  endtask : createEnvironment

  // --------------------------------------------------------------------------
  //                       Test auxilarity procedures
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Resets design
  task resetDesign();
    APP_RST=1;
    QDR_RST=1;                       // Init Reset variable
    #APP_RST_TIME
    APP_RST = 0;
    QDR_RST = 0;                     // Deactivate reset after reset_time
  endtask : resetDesign

  // --------------------------------------------------------------------------
  // Enable test Environment
  task enableTestEnvironment();
    // Enable Driver, Monitor, Coverage for each port
    fluDriver.setEnabled();
    fluMonitor.setEnabled();
    fluResponder.setEnabled();
    //coverage.setEnabled();
    //fifoCoverage.setEnabled();
  endtask : enableTestEnvironment

  // --------------------------------------------------------------------------
  // Disable test Environment
  task disableTestEnvironment();
     // Disable drivers
     #(1000*APP_CLK_PERIOD);
     fluDriver.setDisabled();
     // Disable monitors
     #(1000*APP_CLK_PERIOD);
     fluMonitor.setDisabled();
     fluResponder.setDisabled();
     //coverage.setDisabled();
     //fifoCoverage.setDisabled();
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
       #(APP_CLK_PERIOD);

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
     //coverage.display();
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
    #(10000*APP_CLK_PERIOD);

    // Disable Test Enviroment
    disableTestEnvironment();

    // Display Scoreboard
    scoreboard.display();
    //coverage.display();
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
    #(2000*APP_CLK_PERIOD);

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

