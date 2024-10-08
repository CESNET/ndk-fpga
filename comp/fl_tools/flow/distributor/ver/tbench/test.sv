/*
 * test.sv: FL_DISTRIBUTOR automatic test
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
program TEST (
  input  logic     CLK,
  output logic     RESET,
  iFrameLinkRx.tb  RX,
  iFrameLinkTx.tb  TX[OUTPUT_COUNT],
  iFrameLinkTx.monitor  MONITOR[OUTPUT_COUNT]
  );

  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------

  FrameLinkTransaction                          flBlueprint;
  Generator                                     generator;
  FrameLinkDriver  #(DATA_WIDTH, DREM_WIDTH)    flDriver;
  FrameLinkMonitor #(DATA_WIDTH, DREM_WIDTH)    flMonitor[OUTPUT_COUNT];
  FrameLinkResponder #(DATA_WIDTH, DREM_WIDTH)  flResponder[OUTPUT_COUNT];
  Coverage #(DATA_WIDTH,DREM_WIDTH,DATA_WIDTH,DREM_WIDTH) coverage;
  Scoreboard #(OUTPUT_COUNT,DEFAULT_IFC,INUM_OFFSET)      scoreboard;

  // Only array of virtual interfaces can be indexed
  virtual iFrameLinkTx.tb      #(DATA_WIDTH, DREM_WIDTH) vTX[OUTPUT_COUNT];
  virtual iFrameLinkTx.monitor #(DATA_WIDTH, DREM_WIDTH) vMONITOR[OUTPUT_COUNT];

  // --------------------------------------------------------------------------
  //                       Creating Environment tasks
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Create Test Environment
  task createGeneratorEnvironment(int packet_count = GENERATOR_FL_PACKET_COUNT,
                                  int packet_size_max[] = GENERATOR_FL_PACKET_SIZE_MAX,
                                  int packet_size_min[] = GENERATOR_FL_PACKET_SIZE_MIN
                                  );
  // Create generator
    generator= new("Generator", 0);
    flBlueprint = new;
    flBlueprint.packetCount   = packet_count;
    flBlueprint.packetSizeMax = packet_size_max;
    flBlueprint.packetSizeMin = packet_size_min;
    generator.blueprint = flBlueprint;
  endtask: createGeneratorEnvironment

  // Create Test Environment
  task createEnvironment();
    // Assign virtual interfaces
    vTX      = TX;
    vMONITOR = MONITOR;

    // Coverage class
    coverage = new();
    // Create scoreboard
    scoreboard = new;

    // Create and connect driver
    flDriver       = new ("Driver0", generator.transMbx, RX);
      flDriver.txDelayEn_wt             = DRIVER_DELAYEN_WT;
      flDriver.txDelayDisable_wt        = DRIVER_DELAYDIS_WT;
      flDriver.txDelayLow               = DRIVER_DELAYLOW;
      flDriver.txDelayHigh              = DRIVER_DELAYHIGH;
      flDriver.insideTxDelayEn_wt       = DRIVER_INSIDE_DELAYEN_WT;
      flDriver.insideTxDelayDisable_wt  = DRIVER_INSIDE_DELAYDIS_WT;
      flDriver.insideTxDelayLow         = DRIVER_INSIDE_DELAYLOW;
      flDriver.insideTxDelayHigh        = DRIVER_INSIDE_DELAYHIGH;
      flDriver.setCallbacks(scoreboard.driverCbs);
      coverage.addFrameLinkInterfaceRx(RX,"RXcoverage");

    // Create and connect monitor and responder
    for(int i=0; i<OUTPUT_COUNT; i++) begin
      string monitorLabel;
      string responderLabel;

      monitorLabel   = $sformatf("Monitor %0d", i);
      responderLabel = $sformatf("Responder %0d", i);
      flMonitor[i]   = new (monitorLabel, vMONITOR[i]);
      flResponder[i] = new (responderLabel, vTX[i]);

      flResponder[i].rxDelayEn_wt            = MONITOR_DELAYEN_WT;
      flResponder[i].rxDelayDisable_wt       = MONITOR_DELAYDIS_WT;
      flResponder[i].rxDelayLow              = MONITOR_DELAYLOW;
      flResponder[i].rxDelayHigh             = MONITOR_DELAYHIGH;
      flResponder[i].insideRxDelayEn_wt      = MONITOR_INSIDE_DELAYEN_WT;
      flResponder[i].insideRxDelayDisable_wt = MONITOR_INSIDE_DELAYDIS_WT;
      flResponder[i].insideRxDelayLow        = MONITOR_INSIDE_DELAYLOW;
      flResponder[i].insideRxDelayHigh       = MONITOR_INSIDE_DELAYHIGH;
      flMonitor[i].setCallbacks(scoreboard.monitorCbs);
      coverage.addFrameLinkInterfaceTx(vMONITOR[i],"TXcoverage0");
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
  // Enable test Enviroment
  task enableTestEnvironment();
    // Enable Driver, Monitor, Coverage for each port
    flDriver.setEnabled();
    for(int i=0; i<OUTPUT_COUNT; i++) begin
      flMonitor[i].setEnabled();
      flResponder[i].setEnabled();
    end
    coverage.setEnabled();
  endtask : enableTestEnvironment

  // --------------------------------------------------------------------------
  // Disable test Enviroment
  task disableTestEnvironment();
    bit busy;
    int i;

    i = 0;

    // Disable drivers
    #(1000*CLK_PERIOD);
    flDriver.setDisabled();

    // Check if monitors are not receiving transaction for 100 CLK_PERIODs
    while (i<100) begin
      busy = 0;
      for (int j=0; j<OUTPUT_COUNT; j++)
        if (flMonitor[j].busy == 1)
          busy = 1;
      if (busy)
        i = 0;
      else i++;
      #(CLK_PERIOD);
    end

    // Disable monitors
    for(int i=0; i<OUTPUT_COUNT; i++) begin
      flMonitor[i].setDisabled();
      flResponder[i].setDisabled();
    end

    coverage.setDisabled();
  endtask : disableTestEnvironment

  // --------------------------------------------------------------------------
  //                            Test cases
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Test Case 1
  task test1();
     $write("\n\n############ TEST CASE 1 ############\n\n");
     // Enable Test enviroment
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
    $write("\n\n############ GENERICS ############\n\n");
    $write("DATA_WIDTH:\t%1d\nOUTPUT_COUNT:\t%1d\nDEFAULT_IFC:\t%1d\nINUM_OFFSET:\t%1d\nPARTS:\t%1d\n",DATA_WIDTH,OUTPUT_COUNT,DEFAULT_IFC,INUM_OFFSET,PARTS);
    test1();       // Run Test 1

    // -------------------------------------
    // STOP TESTING
    // -------------------------------------

    $write("Verification finished successfully!\n");
    $stop();       // Stop testing
  end

endprogram

