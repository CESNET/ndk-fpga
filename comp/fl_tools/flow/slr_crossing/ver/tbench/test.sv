/*!
 * \file test.sv
 * \brief Test Cases
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2014
 */
/*
 * Copyright (C) 2014 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

import sv_common_pkg::*;
import sv_fl_pkg::*;
import test_pkg::*;

program TEST (
    input  logic     CLK,
    output logic     RESET,
    iFrameLinkRx.tb  RX,
    iFrameLinkTx.tb  TX,
    iFrameLinkTx.monitor MONITOR
  );

  FrameLinkTransaction                 flBlueprint;
  Generator                            generator;
  FrameLinkDriver #(DATA_WIDTH, DREM_WIDTH)     flDriver;
  FrameLinkMonitor #(DATA_WIDTH, DREM_WIDTH)    flMonitor;
  FrameLinkResponder #(DATA_WIDTH, DREM_WIDTH)  flResponder;
  Scoreboard                           scoreboard;
  Coverage #(DATA_WIDTH,DREM_WIDTH,DATA_WIDTH,DREM_WIDTH) coverage;

  // --------------------------------------------------------------------------
  // Create Test Environment
  task createGeneratorEnvironment(int packet_count = GENERATOR_FL_PACKET_COUNT, int packet_size_max[] = GENERATOR_FL_PACKET_SIZE_MAX, int packet_size_min[] = GENERATOR_FL_PACKET_SIZE_MIN);
    generator = new("Generator", 0);
     flBlueprint = new;
     flBlueprint.packetCount   = packet_count;
     flBlueprint.packetSizeMax = packet_size_max;
     flBlueprint.packetSizeMin = packet_size_min;
     generator.blueprint       = flBlueprint;
  endtask: createGeneratorEnvironment

  task createEnvironment();
    flDriver  = new ("Driver", generator.transMbx, RX);
     flDriver.txDelayEn_wt             = DRIVER_DELAYEN_WT;
     flDriver.txDelayDisable_wt        = DRIVER_DELAYDIS_WT;
     flDriver.txDelayLow               = DRIVER_DELAYLOW;
     flDriver.txDelayHigh              = DRIVER_DELAYHIGH;
     flDriver.insideTxDelayEn_wt       = DRIVER_INSIDE_DELAYEN_WT;
     flDriver.insideTxDelayDisable_wt  = DRIVER_INSIDE_DELAYDIS_WT;
     flDriver.insideTxDelayLow         = DRIVER_INSIDE_DELAYLOW;
     flDriver.insideTxDelayHigh        = DRIVER_INSIDE_DELAYHIGH;
    flMonitor = new ("Monitor", MONITOR);
    flResponder = new ("Responder", TX);
     flResponder.rxDelayEn_wt            = MONITOR_DELAYEN_WT;
     flResponder.rxDelayDisable_wt       = MONITOR_DELAYDIS_WT;
     flResponder.rxDelayLow              = MONITOR_DELAYLOW;
     flResponder.rxDelayHigh             = MONITOR_DELAYHIGH;
     flResponder.insideRxDelayEn_wt      = MONITOR_INSIDE_DELAYEN_WT;
     flResponder.insideRxDelayDisable_wt = MONITOR_INSIDE_DELAYDIS_WT;
     flResponder.insideRxDelayLow        = MONITOR_INSIDE_DELAYLOW;
     flResponder.insideRxDelayHigh       = MONITOR_INSIDE_DELAYHIGH;
    scoreboard = new;
    coverage = new();
     coverage.addFrameLinkInterfaceRx(RX,"RXcoverage");
     coverage.addFrameLinkInterfaceTx(MONITOR,"TXcoverage");
    flDriver.setCallbacks(scoreboard.driverCbs);
    flMonitor.setCallbacks(scoreboard.monitorCbs);
  endtask : createEnvironment

  // --------------------------------------------------------------------------
  // Resets design
  task resetDesign();
    RESET=1;
    #RESET_TIME     RESET = 0;
  endtask : resetDesign

  // --------------------------------------------------------------------------
  // Enable test Environment
  task enableTestEnvironment();
    flDriver.setEnabled();
    flMonitor.setEnabled();
    flResponder.setEnabled();
    coverage.setEnabled();
  endtask : enableTestEnvironment

  // --------------------------------------------------------------------------
  // Disable test Environment
  task disableTestEnvironment();
    int i;
    i = 0;
    while (i<100) begin
      if (generator.enabled || flDriver.busy || flMonitor.busy) i=0; else i++;
      #(CLK_PERIOD);
    end
    flDriver.setDisabled();
    flMonitor.setDisabled();
    flResponder.setDisabled();
    coverage.setDisabled();
  endtask : disableTestEnvironment

  // --------------------------------------------------------------------------
  // Test Case 1
  task test1();
    $write("\n\n############ TEST CASE 1 ############\n\n");
    createGeneratorEnvironment();
    createEnvironment();
    enableTestEnvironment();
    generator.setEnabled(TRANSACTION_COUT);
    disableTestEnvironment();
    scoreboard.display();
    coverage.display();
  endtask: test1

  // --------------------------------------------------------------------------
  // Test Case 2
  task test2();
    $write("\n\n############ TEST CASE 2 ############\n\n");
    createGeneratorEnvironment(1,'{8},'{1});
    createEnvironment();
    enableTestEnvironment();
    generator.setEnabled(TRANSACTION_COUT);
    disableTestEnvironment();
    scoreboard.display();
    coverage.display();
  endtask: test2

  // --------------------------------------------------------------------------
  //                           Main test part
  // --------------------------------------------------------------------------
  initial begin
    resetDesign();
    test1();
    resetDesign();
    test2();
    $write("Verification finished successfully!\n");
    $stop();
  end

endprogram

