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

import test_pkg::*;
import sv_common_pkg::*;
import sv_flu_pkg::*;


// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
program TEST (
   input logic CLK,
   output logic RESET,
   iFrameLinkURx.tb         RX[PORTS],
   iFrameLinkURx.tb         RXHDR[PORTS],
   iFrameLinkUTx.tb         TX,
   iFrameLinkUTx.monitor    MONITOR,
   iFrameLinkUTx.tb         TXHDR,
   iFrameLinkUTx.monitor    MONITORHDR
  );

  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------

  FrameLinkUTransaction                fluBlueprint[PORTS];                         // Transaction
  FrameLinkUTransaction                fluhdrBlueprint;
  Generator                            generator[PORTS];                            // Generator
  Generator                            generator_hdr[PORTS];
  FrameLinkUDriver   #(DRIVER0_DATA_WIDTH, DRIVER0_EOP_WIDTH, DRIVER0_SOP_WIDTH)            fluDriver[PORTS];    // Driver
  FrameLinkUDriver   #(DRIVER_HDR_DATA_WIDTH,DRIVER_HDR_EOP_WIDTH,DRIVER_HDR_SOP_WIDTH)     fluhdrDriver[PORTS];
  FrameLinkUMonitor  #(DRIVER0_DATA_WIDTH, DRIVER0_EOP_WIDTH, DRIVER0_SOP_WIDTH)            fluMonitor;          // Monitor
  FrameLinkUMonitor   #(DRIVER_HDR_DATA_WIDTH,DRIVER_HDR_EOP_WIDTH,DRIVER_HDR_SOP_WIDTH)    fluhdrMonitor;
  FrameLinkUResponder #(DRIVER0_DATA_WIDTH, DRIVER0_EOP_WIDTH, DRIVER0_SOP_WIDTH)           fluResponder;        // Responder
  FrameLinkUResponder  #(DRIVER_HDR_DATA_WIDTH,DRIVER_HDR_EOP_WIDTH,DRIVER_HDR_SOP_WIDTH)   fluhdrResponder;
  Scoreboard                           scoreboard;                              // Scoreboard

   virtual iFrameLinkURx.tb      #(DRIVER0_DATA_WIDTH, DRIVER0_EOP_WIDTH, DRIVER0_SOP_WIDTH)        vRX[PORTS];
   virtual iFrameLinkURx.tb      #(DRIVER_HDR_DATA_WIDTH,DRIVER_HDR_EOP_WIDTH,DRIVER_HDR_SOP_WIDTH) vRX_hdr[PORTS];

  // --------------------------------------------------------------------------
  //                       Creating Environment tasks
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Create Test Environment
  task createGeneratorEnvironment(int packet_size_max = GENERATOR0_FLU_PACKET_SIZE_MAX,
                                  int packet_size_min = GENERATOR0_FLU_PACKET_SIZE_MIN
                                  );
  // Create data generator
    for (int i=0; i<PORTS; i++) begin
    generator[i] = new("Generator", i);
      fluBlueprint[i] = new;
      fluBlueprint[i].packetSizeMax = packet_size_max;
      fluBlueprint[i].packetSizeMin = packet_size_min;
      generator[i].blueprint       = fluBlueprint[i];
    end;

   // Create header generator
   fluhdrBlueprint = new;
   fluhdrBlueprint.packetSizeMin = GENERATOR_FL_PACKET_SIZE_MIN;
   fluhdrBlueprint.packetSizeMax = GENERATOR_FL_PAKCET_SIZE_MAX;

   for (int i=0;i<PORTS;i++) begin
      generator_hdr[i] = new("Hdr Generator",i);
      generator_hdr[i].blueprint = fluhdrBlueprint;
   end
  endtask: createGeneratorEnvironment

  task createEnvironment();
    int unsigned enableAlign;
    string driverLabel;

    vRX=RX;
    vRX_hdr = RXHDR;

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

      // Get the information about aligning (& 1 means anding with mash 0000..001)
      enableAlign = (ALIGN_MAP >> i) & 1;
      fluDriver[i].startPositionLow         = DRIVER0_START_POS_LOW*enableAlign;
      fluDriver[i].startPositionHigh        = DRIVER0_START_POS_HIGH*enableAlign;

      driverLabel = $sformatf( "Hdr Driver %0d",i);
      fluhdrDriver[i] = new (driverLabel, generator_hdr[i].transMbx, vRX_hdr[i]);
      fluhdrDriver[i].insideTxDelayEn_wt       = DRIVER_HDR_INSIDE_DELAYEN_WT;
      fluhdrDriver[i].insideTxDelayDisable_wt  = DRIVER_HDR_INSIDE_DELAYDIS_WT;
      fluhdrDriver[i].insideTxDelayLow         = DRIVER_HDR_INSIDE_DELAYLOW;
      fluhdrDriver[i].insideTxDelayHigh        = DRIVER_HDR_INSIDE_DELAYHIGH;
      fluhdrDriver[i].startPositionLow         = DRIVER_HDR_START_POS_LOW;
      fluhdrDriver[i].startPositionHigh        = DRIVER_HDR_START_POS_HIGH;

    fluDriver[i].setCallbacks(scoreboard.driverCbs);
    fluhdrDriver[i].setCallbacks(scoreboard.driverCbs);
    end;

   // Create and connect monitor and responder
      fluMonitor   = new ("Monitor0", MONITOR);
      fluResponder = new ("Responder0", TX);
      fluhdrMonitor   = new ("Monitor1",MONITORHDR);
      fluhdrResponder = new ("Responder1", TXHDR);

      fluResponder.rxDelayEn_wt            = MONITOR0_DELAYEN_WT;
      fluResponder.rxDelayDisable_wt       = MONITOR0_DELAYDIS_WT;
      fluResponder.rxDelayLow              = MONITOR0_DELAYLOW;
      fluResponder.rxDelayHigh             = MONITOR0_DELAYHIGH;
      fluResponder.insideRxDelayEn_wt      = MONITOR0_INSIDE_DELAYEN_WT;
      fluResponder.insideRxDelayDisable_wt = MONITOR0_INSIDE_DELAYDIS_WT;
      fluResponder.insideRxDelayLow        = MONITOR0_INSIDE_DELAYLOW;
      fluResponder.insideRxDelayHigh       = MONITOR0_INSIDE_DELAYHIGH;

      fluhdrResponder.rxDelayEn_wt            = MONITOR_HDR_DELAYEN_WT;
      fluhdrResponder.rxDelayDisable_wt       = MONITOR_HDR_DELAYDIS_WT;
      fluhdrResponder.rxDelayLow              = MONITOR_HDR_DELAYLOW;
      fluhdrResponder.rxDelayHigh             = MONITOR_HDR_DELAYHIGH;
      fluhdrResponder.insideRxDelayEn_wt      = MONITOR_HDR_INSIDE_DELAYEN_WT;
      fluhdrResponder.insideRxDelayDisable_wt = MONITOR_HDR_INSIDE_DELAYDIS_WT;
      fluhdrResponder.insideRxDelayLow        = MONITOR_HDR_INSIDE_DELAYLOW;
      fluhdrResponder.insideRxDelayHigh       = MONITOR_HDR_INSIDE_DELAYHIGH;

      fluMonitor.setCallbacks(scoreboard.monitorCbs);
      fluhdrMonitor.setCallbacks(scoreboard.monitorCbs);

      // Setup the flu Monitor
      if(RESERVE_GAP_EN == TRUE) fluMonitor.enableGapDetection(GAP_SIZE_MIN,GAP_SIZE_MAX);
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
    // Data driver, monitor, responder
    for(int i=0; i<PORTS; i++) fluDriver[i].setEnabled();
    fluMonitor.setEnabled();
    fluResponder.setEnabled();

    // Heade drive, monitor, responder
    if(HDR_ENABLE == TRUE) begin
      for(int i=0;i<PORTS;i++) fluhdrDriver[i].setEnabled();
      fluhdrMonitor.setEnabled();
      fluhdrResponder.setEnabled();
    end
  endtask : enableTestEnvironment

  // --------------------------------------------------------------------------
  // Disable test Environment
  task disableTestEnvironment();
     #(1000*CLK_PERIOD);
     for(int i=0; i<PORTS; i++) fluDriver[i].setDisabled();
     fluMonitor.setDisabled();
     fluResponder.setDisabled();

     if(HDR_ENABLE == TRUE) begin
      for(int i=0;i<PORTS;i++) fluhdrDriver[i].setDisabled();
      fluhdrMonitor.setDisabled();
      fluhdrResponder.setDisabled();
     end
  endtask : disableTestEnvironment

  // Run all generators
  task runGenerators();
     for(int i=0; i<PORTS; i++) generator[i].setEnabled(TRANSACTION_COUNT);
     if(HDR_ENABLE == TRUE) begin
      for(int i=0;i<PORTS; i++) generator_hdr[i].setEnabled(TRANSACTION_COUNT);
     end

  endtask : runGenerators

  // Wait and disable all generators
  task waitAndDisableGenerators();
     // Pokud je generator aktivni nic nedelej
     for(int i=0; i<PORTS; i++) wait (generator[i].enabled == 0);
     if(HDR_ENABLE == TRUE) begin
      for(int i=0;i<PORTS; i++) wait (generator_hdr[i].enabled == 0);
     end
  endtask : waitAndDisableGenerators

  // --------------------------------------------------------------------------
  //                            Test cases
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Test Case 1
  task test1();
     $write("\n\n############ TEST CASE 1 ############\n\n");
     // Enable Test environment
     enableTestEnvironment();
     // Start Test
      runGenerators();
      waitAndDisableGenerators();

     // Disable Test Enviroment
     disableTestEnvironment();

     // Display Scoreboard
     scoreboard.display();
  endtask: test1

  // --------------------------------------------------------------------------
  // Test Case 2
  // Classic length transactions, slow TX and fast RX
  task test2();
    $write("\n\n############ TEST CASE 2 ############\n\n");

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

     // Start Test
      runGenerators();
      waitAndDisableGenerators();

    // Disable Test Enviroment
    disableTestEnvironment();

    // Display Scoreboard
    scoreboard.display();
  endtask: test2

  // --------------------------------------------------------------------------
  // Test Case 3
  // Classic length transactions, no TX wait
  task test3();
    $write("\n\n############ TEST CASE 3 ############\n\n");

    // create & enable environment
    createGeneratorEnvironment();
    createEnvironment();

    // set zero delays
    fluResponder.rxDelayEn_wt        = 0;
    fluResponder.insideRxDelayEn_wt  = 0;

    // Enable Test environment
    enableTestEnvironment();

    // Start Test
     runGenerators();
     waitAndDisableGenerators();

     // Disable Test Enviroment
    disableTestEnvironment();

    // Display Scoreboard
    scoreboard.display();
  endtask: test3

  // --------------------------------------------------------------------------
  // Test Case 4
  // Classic length transactions, lot of waiting
  task test4();
    $write("\n\n############ TEST CASE 4 ############\n\n");

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

     // Start Test
      runGenerators();
      waitAndDisableGenerators();

    // Disable Test Enviroment
    disableTestEnvironment();

    // Display Scoreboard
    scoreboard.display();
  endtask: test4

    // --------------------------------------------------------------------------
  // Test Case 5
  // Classic length transactions, fast RX0 and TX, slow other RXs
  task test5();
    $write("\n\n############ TEST CASE 5 ############\n\n");

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

    // Start Test
      runGenerators();
      waitAndDisableGenerators();

    // Disable Test Enviroment
    disableTestEnvironment();

    // Display Scoreboard
    scoreboard.display();
  endtask: test5

  // --------------------------------------------------------------------------
  // Test Case 6
  // Classical Ethernet Frame transaction, no TX wait, fast RX
  task test6();
    $write("\n\n############ TEST CASE 6 ############\n\n");

    // create & enable environment
    createGeneratorEnvironment(1500,60);
    createEnvironment();

    // set zero delays
    fluResponder.rxDelayEn_wt        = 0;
    fluResponder.insideRxDelayEn_wt  = 0;

    fluResponder.rxDelayEn_wt            = 0;
    fluResponder.insideRxDelayEn_wt      = 0;

    for(int i=0; i<PORTS; i++)
    fluDriver[i].insideTxDelayEn_wt =0;

    // Enable Test environment
    enableTestEnvironment();

     // Start Test
      runGenerators();
      waitAndDisableGenerators();

     // Disable Test Enviroment
    disableTestEnvironment();

    // Display Scoreboard
    scoreboard.display();
  endtask: test6

  // --------------------------------------------------------------------------
  // Test Case 7
  // Generate very short packets
  task test7();
     $write("\n\n############ TEST CASE 7 ############\n\n");
     // Create Generator Environment
     createGeneratorEnvironment(8,1);

     // Create Test environment
     createEnvironment();
     // Enable Test environment
     enableTestEnvironment();

     // Start Test
      runGenerators();
      waitAndDisableGenerators();

     // Disable Test Environment
     disableTestEnvironment();
     // Display Scoreboard
     scoreboard.display();
  endtask: test7

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
    test5();
    test6();

    // Last test with very short packets will be run if and only if
    // the 128 bit gap is not reserved
    if(RESERVE_GAP_EN == FALSE ) test7();

    // -------------------------------------
    // STOP TESTING
    // -------------------------------------
    $stop();       // Stop testing
  end

endprogram

