/*!
 * \file test.sv
 * \brief Test Cases
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2018
 */
/*
 * Copyright (C) 2018 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

import sv_common_pkg::*;
import sv_flu_pkg::*;
import sv_wl_pkg::*;
import test_pkg::*;

program TEST (
    input  logic      CLK,
    output logic      RESET,
    iFrameLinkURx.tb  RX,
    iWordLinkTx.tb  TX,
    iWordLinkTx.monitor MONITOR
  );

  FrameLinkUTransaction                 fluBlueprint;
  Generator                             generator;
  FrameLinkUDriver #(DATA_WIDTH, EOP_POS_WIDTH, SOP_POS_WIDTH)     fluDriver;
  WordLinkMonitor #(16)    fluMonitor;
  WordLinkResponder #(16)  fluResponder;
  Scoreboard                            scoreboard;

  // --------------------------------------------------------------------------
  // Create Test Environment
  task createGeneratorEnvironment(int packet_size_max = GENERATOR_FLU_PACKET_SIZE_MAX, int packet_size_min = GENERATOR_FLU_PACKET_SIZE_MIN);
    generator = new("Generator", 0);
     fluBlueprint = new;
     fluBlueprint.packetSizeMax = packet_size_max;
     fluBlueprint.packetSizeMin = packet_size_min;
     generator.blueprint        = fluBlueprint;
  endtask: createGeneratorEnvironment

  task createEnvironment();
    fluDriver  = new ("Driver", generator.transMbx, RX);
     fluDriver.insideTxDelayEn_wt       = DRIVER_INSIDE_DELAYEN_WT;
     fluDriver.insideTxDelayDisable_wt  = DRIVER_INSIDE_DELAYDIS_WT;
     fluDriver.insideTxDelayLow         = DRIVER_INSIDE_DELAYLOW;
     fluDriver.insideTxDelayHigh        = DRIVER_INSIDE_DELAYHIGH;
     fluDriver.startPositionLow         = DRIVER_START_POS_LOW;
     fluDriver.startPositionHigh        = DRIVER_START_POS_HIGH;
    fluMonitor = new ("Monitor", MONITOR);
    fluResponder = new ("Responder", TX);
     fluResponder.rxDelayEn_wt            = MONITOR_DELAYEN_WT;
     fluResponder.rxDelayDisable_wt       = MONITOR_DELAYDIS_WT;
     fluResponder.rxDelayLow              = MONITOR_DELAYLOW;
     fluResponder.rxDelayHigh             = MONITOR_DELAYHIGH;
    scoreboard = new;
    fluDriver.setCallbacks(scoreboard.driverCbs);
    fluMonitor.setCallbacks(scoreboard.monitorCbs);
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
    fluDriver.setEnabled();
    fluMonitor.setEnabled();
    fluResponder.setEnabled();
  endtask : enableTestEnvironment

  // --------------------------------------------------------------------------
  // Disable test Environment
  task disableTestEnvironment();
    int i;
    i = 0;
    while (i<100) begin
      if (generator.enabled || fluDriver.busy || fluMonitor.busy) i=0; else i++;
      #(CLK_PERIOD);
    end
    fluDriver.setDisabled();
    fluMonitor.setDisabled();
    fluResponder.setDisabled();
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
  endtask: test1

  // --------------------------------------------------------------------------
  //                           Main test part
  // --------------------------------------------------------------------------
  initial begin
    resetDesign();
    test1();
    $write("Verification finished successfully!\n");
    $stop();
  end

endprogram

