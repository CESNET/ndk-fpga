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
import sv_flu_pkg::*;
import test_pkg::*;

// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
// V PRIPADE POTREBY DOPLNIT FRAMELINKOVE ROZHRANIA
program TEST (
  input  logic     CLK,
  output logic     RESET,
  output logic[MAX_RATE_L-1:0] RATE,
  input logic      PCKT_DISCARD,
  iFrameLinkURx.tb  RX,
  iFrameLinkUTx.tb  TX,
  iFrameLinkUTx.monitor MONITOR
  );

  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------

  FrameLinkUTransaction                 fluBlueprint;                             // Transaction
  Generator                            generator;                               // Generator
  FrameLinkUDriver #(DRIVER0_DATA_WIDTH, DRIVER0_EOP_WIDTH, DRIVER0_SOP_WIDTH)   fluDriver;       // Driver
  FrameLinkUMonitor #(DRIVER0_DATA_WIDTH, DRIVER0_EOP_WIDTH, DRIVER0_SOP_WIDTH)  fluMonitor;      // Monitor
  FrameLinkUResponder #(DRIVER0_DATA_WIDTH, DRIVER0_EOP_WIDTH, DRIVER0_SOP_WIDTH) fluResponder;  // Responder
  Scoreboard                           scoreboard;                              // Scoreboard
  integer                         discard;
  integer i;

  // --------------------------------------------------------------------------
  //                       Creating Environment tasks
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Create Test Environment
  task createGeneratorEnvironment(int packet_count = GENERATOR0_FLU_PACKET_COUNT,
                                  int packet_size_max = GENERATOR0_FLU_PACKET_SIZE_MAX,
                                  int packet_size_min = GENERATOR0_FLU_PACKET_SIZE_MIN
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
    scoreboard = new(DUT_RATE);
      fluDriver.setCallbacks(scoreboard.driverCbs);
      fluMonitor.setCallbacks(scoreboard.monitorCbs);
  endtask : createEnvironment

  // --------------------------------------------------------------------------
  //                       Test auxilarity procedures
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Resets design
  task resetDesign();
    RESET=1;                       // Init Reset variable
    RATE=DUT_RATE;
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
     fluDriver.setDisabled();
     // Disable monitors
     fluMonitor.setDisabled();
     fluResponder.setDisabled();
     //coverage.setDisabled();
  endtask : disableTestEnvironment

  // --------------------------------------------------------------------------
  //                            Test cases
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Test Case 1
  task test1();
     discard=0;
     $write("\n\n############ TEST CASE 1 ############\n\n");
     // Enable Test environment
     enableTestEnvironment();
     // Run generators
     generator.setEnabled(TRANSACTION_COUNT);

     // Pokud je generator aktivni nic nedelej
     while (generator.enabled) begin
       #(CLK_PERIOD);
       if(PCKT_DISCARD) discard++;
     end
     for(i=0;i<1000;i++) begin
       #(CLK_PERIOD);
       if(PCKT_DISCARD) discard++;
     end

     // Disable Test Enviroment
     disableTestEnvironment();

     // Display Scoreboard
     scoreboard.display();
     $write("Discarded: %d\n",discard);
  endtask: test1

  // --------------------------------------------------------------------------
  // Test Case 2
  // Generate very short packets
  task test2();
     discard=0;
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
     while (generator.enabled) begin
       #(CLK_PERIOD);
       if(PCKT_DISCARD) discard++;
     end
     for(i=0;i<1000;i++) begin
       #(CLK_PERIOD);
       if(PCKT_DISCARD) discard++;
     end

     // Disable Test Environment
     disableTestEnvironment();
     // Display Scoreboard
     scoreboard.display();
     $write("Discarded: %d\n",discard);
  endtask: test2

  // --------------------------------------------------------------------------
  // Test Case 4
  // Classic length transactions, no TX wait
  task test4();
    discard=0;
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
    while (generator.enabled) begin
       #(CLK_PERIOD);
       if(PCKT_DISCARD) discard++;
     end
     for(i=0;i<1000;i++) begin
       #(CLK_PERIOD);
       if(PCKT_DISCARD) discard++;
     end

     // Disable Test Enviroment
    disableTestEnvironment();

    // Display Scoreboard
    scoreboard.display();
    $write("Discarded: %d\n",discard);
  endtask: test4

  // --------------------------------------------------------------------------
  // Test Case 5
  // Classic length transactions, lot of waiting
  task test5();
    discard=0;
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
    while (generator.enabled) begin
       #(CLK_PERIOD);
       if(PCKT_DISCARD) discard++;
     end
     for(i=0;i<1000;i++) begin
       #(CLK_PERIOD);
       if(PCKT_DISCARD) discard++;
     end

    // Disable Test Enviroment
    disableTestEnvironment();

    // Display Scoreboard
    scoreboard.display();
    $write("Discarded: %d\n",discard);
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
    test4();
    test5();

    // -------------------------------------
    // STOP TESTING
    // -------------------------------------
    $stop();       // Stop testing
  end

endprogram

