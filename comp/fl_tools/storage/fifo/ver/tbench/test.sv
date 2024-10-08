/*
 * test.sv: FL_FIFO automatic test
 * Copyright (C) 2007 CESNET
 * Author(s): Petr Kobiersky <kobiersky@liberouter.org>
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
import sv_fl_fifo_pkg::*;
import test_pkg::*;

// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
// V PRIPADE POTREBY DOPLNIT FRAMELINKOVE ROZHRANIA
program TEST (
  input  logic         CLK,
  output logic         RESET,
  iFrameLinkRx.tb      RX,
  iFrameLinkTx.tb      TX,
  iFrameLinkFifo.ctrl  CTRL,
  iFrameLinkTx.monitor MONITOR
  );

  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------

  // AK MA KOMPONENTA VIAC DRIVEROV ALEBO MONITOROV TREBA ICH NA TOMTO
  // MIESTE DEKLAROVAT A V TASKU CREATEENVIRONMENT INSTANCIOVAT

  // Transaction
  FrameLinkTransaction    flBlueprint;
  // Generator
  Generator               generator;
  // Driver
  FrameLinkDriver #(DRIVER0_DATA_WIDTH, DRIVER0_DREM_WIDTH)       flDriver;
  // Monitor
  FrameLinkMonitor #(MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH)    flMonitor;
  // Responder
  FrameLinkResponder #(MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH)  flResponder;
  // Checker
  FrameLinkFifoChecker #(DATA_WIDTH, DREM_WIDTH, BLOCK_SIZE,
                         STATUS_WIDTH, ITEMS, USE_BRAMS)          flChecker;
  // Scoreboard
  Scoreboard              scoreboard;
  // Coverage
  Coverage #(DATA_WIDTH,DREM_WIDTH,DATA_WIDTH,DREM_WIDTH)         coverage;
  FifoCoverage #(STATUS_WIDTH)                                    fifoCoverage;

  // --------------------------------------------------------------------------
  //                       Creating Environment tasks
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Create Generator Environment
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

  // Create Test Environment
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
    // Create checker
    flChecker = new("Checker0", RX, TX, CTRL);
    // Create scoreboard
    scoreboard = new;
    // Coverage class
    coverage = new();
      coverage.addFrameLinkInterfaceRx(RX,"RXcoverage");
      coverage.addFrameLinkInterfaceTx(MONITOR,"TXcoverage");
    fifoCoverage = new();
      fifoCoverage.addFrameLinkInterfaceFifo(CTRL,"CTRLcoverage");
    // Set Callbacks
      flDriver.setCallbacks(scoreboard.driverCbs);
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
    flDriver.setEnabled();
    flMonitor.setEnabled();
    flResponder.setEnabled();
    flChecker.setEnabled();
    coverage.setEnabled();
    fifoCoverage.setEnabled();
  endtask : enableTestEnvironment

  // --------------------------------------------------------------------------
  // Disable test Environment
  task disableTestEnvironment();
     // Disable drivers
     #(1000*CLK_PERIOD);
     flDriver.setDisabled();
     // Disable monitors
     #(1000*CLK_PERIOD);
     flMonitor.setDisabled();
     flResponder.setDisabled();
     flChecker.setDisabled();
     coverage.setDisabled();
     fifoCoverage.setDisabled();
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
     generator.setEnabled(TRANSACTION_COUT);

     // Pokud je generator aktivni nic nedelej
     while (generator.enabled)
       #(CLK_PERIOD);

     // Disable Test Enviroment
     disableTestEnvironment();

     // Display Scoreboard
     scoreboard.display();
     coverage.display();
     fifoCoverage.display();
  endtask: test1

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

    // -------------------------------------
    // STOP TESTING
    // -------------------------------------
    $write("Verification finished successfully!\n");
    $stop();       // Stop testing
  end

endprogram

