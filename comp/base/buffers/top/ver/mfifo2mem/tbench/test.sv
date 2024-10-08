/*
 * test.sv: Automatic test
 * Copyright (C) 2010 CESNET
 * Author(s): Marek Santa <santa@liberouter.org>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 * TODO:
 *
 */

import sv_buffer_pkg::*;
import test_pkg::*;
import sv_common_pkg::*;


// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
program TEST (
  input  logic           CLK,
  output logic           RESET,
  iNFifoTx.fifo_write_tb FW,
  iMemRead.tb            MR
  );

  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------

  // Transaction
  BufferTransaction                                              buffBlueprint;
  // Generator
  Generator                                                      generator;
  // Driver
  FifoDriver #(DRIVER0_DATA_WIDTH,DRIVER0_FLOWS,DRIVER0_BLOCK_SIZE,
                 DRIVER0_LUT_MEMORY, 0)                          fDriver;
  // Monitor
  MemMonitorNew #(MONITOR0_DATA_WIDTH,MONITOR0_FLOWS,MONITOR0_BLOCK_SIZE,
                 MONITOR0_LUT_MEMORY, MONITOR0_OUTPUT_REG)
                                                                 memMonitor;
  // Scoreboard
  Scoreboard                                                     scoreboard;
  // Coverage
  Coverage #(DATA_WIDTH,FLOWS,BLOCK_SIZE,LUT_MEMORY, 0)        coverage;

  // --------------------------------------------------------------------------
  //                       Creating Environment tasks
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Create Test Environment
  task createEnvironment();
    // Create generator
    generator = new("Generator0", 0);
    buffBlueprint = new;
    buffBlueprint.dataSize   = GENERATOR0_DATA_SIZE;
    buffBlueprint.flowCount  = GENERATOR0_FLOW_COUNT;
    generator.blueprint      = buffBlueprint;

    // Create scoreboard
    scoreboard = new;

    // Coverage class
    coverage = new();

    // Create and connect driver
    fDriver = new ("Driver0", generator.transMbx, FW);
    fDriver.fwDelayEn_wt             = DRIVER0_DELAYEN_WT;
    fDriver.fwDelayDisable_wt        = DRIVER0_DELAYDIS_WT;
    fDriver.fwDelayLow               = DRIVER0_DELAYLOW;
    fDriver.fwDelayHigh              = DRIVER0_DELAYHIGH;
    fDriver.setCallbacks(scoreboard.driverCbs);
    coverage.addGeneralInterfaceWrite(FW,"MFIFO Coverage");

    // Create and connect monitor
    memMonitor = new ("Monitor", MR);
      memMonitor.readDelayEn_wt             = MONITOR0_DELAYEN_WT;
      memMonitor.readDelayDisable_wt        = MONITOR0_DELAYDIS_WT;
      memMonitor.pipeDelayEn_wt             = MONITOR0_PIPEEN_WT;
      memMonitor.pipeDelayDisable_wt        = MONITOR0_PIPEDIS_WT;
    memMonitor.setCallbacks(scoreboard.monitorCbs);
    coverage.addGeneralInterfaceMonitor(MR,"MEM Coverage");

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
    fDriver.setEnabled();
    memMonitor.setEnabled();
    coverage.setEnabled();
  endtask : enableTestEnvironment

  // --------------------------------------------------------------------------
  // Disable test Enviroment
  task disableTestEnvironment();
    // Disable drivers
    #(100*CLK_PERIOD);
    fDriver.setDisabled();

    // Wait while all transaction are received
    finishReceiving();

    memMonitor.setDisabled();
    coverage.setDisabled();
  endtask : disableTestEnvironment

  // --------------------------------------------------------------------------
  // Finish receiving
  task finishReceiving();
    int i;

    i = 0;
    // Check if monitor is not receiving transaction for 100 CLK_PERIODs
    while (i<100) begin
      if (memMonitor.busy)
        i = 0;
      else i++;
      #(CLK_PERIOD);
    end
  endtask : finishReceiving

  // --------------------------------------------------------------------------
  //                            Test cases
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Test Case 1
  task test1();
    $write("\n\n############ TEST CASE 1 ############\n\n");
    $write("## Part 1: Delays on interfaces from test_pkg.\n");
    // Enable Test enviroment
    enableTestEnvironment();
    // Run generators
    generator.setEnabled(TRANSACTION_COUNT);

    // Wait while generator generates transactions
    while (generator.enabled)
      #(CLK_PERIOD);

    // Wait while all transaction are received
    finishReceiving();
    // Display Scoreboard
    scoreboard.display();

    // -----
    $write("\n## Part 2: No delays on interfaces.\n");
    // No delays on input interface
    fDriver.fwDelayEn_wt             = 0;
    fDriver.fwDelayDisable_wt        = 1;

    // No delays on output interface
    memMonitor.readDelayEn_wt        = 0;
    memMonitor.readDelayDisable_wt   = 1;
    memMonitor.pipeDelayEn_wt        = 0;
    memMonitor.pipeDelayDisable_wt   = 1;

    // Run generators
    @(fDriver.f_w.fifo_write_cb);         // Synchronize driver
    generator.setEnabled(TRANSACTION_COUNT);

    // Wait while generator generates transactions
    while (generator.enabled)
      #(CLK_PERIOD);

    // Wait while all transaction are received
    finishReceiving();
    // Display Scoreboard
    scoreboard.display();

    // -----
    $write("\n## Part 3: Delays on output interface only.\n");
    // No delays on input interface
    fDriver.fwDelayEn_wt             = 0;
    fDriver.fwDelayDisable_wt        = 1;

    // Delays on output interface
    memMonitor.readDelayEn_wt        = 1;
    memMonitor.readDelayDisable_wt   = 2;
    memMonitor.pipeDelayEn_wt        = 1;
    memMonitor.pipeDelayDisable_wt   = 2;

    // Run generators
    @(fDriver.f_w.fifo_write_cb);          // Synchronize driver
    generator.setEnabled(TRANSACTION_COUNT);

    // Wait while generator generates transactions
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


