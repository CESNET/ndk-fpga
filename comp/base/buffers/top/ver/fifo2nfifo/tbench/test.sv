/*
 * test.sv: Automatic test
 * Copyright (C) 2008 CESNET
 * Author(s): Marcela Simkova <xsimko03@stud.fit.vutbr.cz>
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
import math_pkg::*;

// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
program TEST (
  input  logic           CLK,
  output logic           RESET,
  iNFifoTx.fifo_write_tb FW,
  iNFifoTx.nfifo_read_tb FR[FLOWS],
  iNFifoTx.nfifo_monitor MONITOR[FLOWS]
  );

  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------
  // AK MA KOMPONENTA VIAC DRIVEROV ALEBO MONITOROV TREBA ICH NA TOMTO MIESTE DEKLAROVAT A V TASKU
  // CREATEENVIRONMENT INSTANCIOVAT

  // Transaction
  BufferTransaction                                                   buffBlueprint;
  // Generator
  Generator                                                           generator;
  // Driver
  FifoDriver #(DRIVER0_DATA_WIDTH,DRIVER0_FLOWS,DRIVER0_BLOCK_SIZE,
                 DRIVER0_LUT_MEMORY, DRIVER0_GLOB_STATE)              fDriver;
  // Monitor
  nFifoMonitor #(MONITOR0_DATA_WIDTH,MONITOR0_FLOWS,MONITOR0_BLOCK_SIZE,
                 MONITOR0_LUT_MEMORY, MONITOR0_GLOB_STATE)            fMonitor[FLOWS];
  // Responder
  nFifoResponder #(MONITOR0_DATA_WIDTH,MONITOR0_FLOWS,MONITOR0_BLOCK_SIZE,
                  MONITOR0_LUT_MEMORY, MONITOR0_GLOB_STATE)           fResponder[FLOWS];
  // Scoreboard
  Scoreboard                                                          scoreboard;
  // Coverage
  Coverage #(DATA_WIDTH,FLOWS,BLOCK_SIZE,LUT_MEMORY,GLOB_STATE)       coverage;

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

    // Create driver
    fDriver = new ("Driver0", generator.transMbx, FW);
    fDriver.fwDelayEn_wt             = DRIVER0_DELAYEN_WT;
    fDriver.fwDelayDisable_wt        = DRIVER0_DELAYDIS_WT;
    fDriver.fwDelayLow               = DRIVER0_DELAYLOW;
    fDriver.fwDelayHigh              = DRIVER0_DELAYHIGH;
    fDriver.setCallbacks(scoreboard.driverCbs);

    // Create monitor
    // MUST BE CONSTANTS :(
    fMonitor[0] = new ("Monitor0", 0, MONITOR[0]);
    fMonitor[1] = new ("Monitor1", 1, MONITOR[1]);
/*    fMonitor[2] = new ("Monitor2", 2, MONITOR[2]);
    fMonitor[3] = new ("Monitor3", 3, MONITOR[3]);
    fMonitor[4] = new ("Monitor4", 4, MONITOR[4]);
    fMonitor[5] = new ("Monitor5", 5, MONITOR[5]);
    fMonitor[6] = new ("Monitor6", 6, MONITOR[6]);
    fMonitor[7] = new ("Monitor7", 7, MONITOR[7]);
*/
    // Create responder
    // MUST BE CONSTANTS :(
    fResponder[0] = new ("Responder0", FR[0]);
    fResponder[1] = new ("Responder1", FR[1]);
/*    fResponder[2] = new ("Responder2", FR[2]);
    fResponder[3] = new ("Responder3", FR[3]);
    fResponder[4] = new ("Responder4", FR[4]);
    fResponder[5] = new ("Responder5", FR[5]);
    fResponder[6] = new ("Responder6", FR[6]);
    fResponder[7] = new ("Responder7", FR[7]);
*/
    // Connect monitors and responders
    for(int i=0; i<FLOWS; i++) begin
      fResponder[i].frDelayEn_wt               = MONITOR0_DELAYEN_WT;
      fResponder[i].frDelayDisable_wt          = MONITOR0_DELAYDIS_WT;
      fResponder[i].frDelayLow                 = MONITOR0_DELAYLOW;
      fResponder[i].frDelayHigh                = MONITOR0_DELAYHIGH;
      fMonitor[i].setCallbacks(scoreboard.monitorCbs);
    end;

    // Coverage class
    coverage = new();
    coverage.addGeneralInterfaceWrite(FW,"FWcoverage");
    coverage.addGeneralInterfaceMonitor(MONITOR[0],"FRcoverage0");
    coverage.addGeneralInterfaceMonitor(MONITOR[1],"FRcoverage1");
/*    coverage.addGeneralInterfaceMonitor(MONITOR[2],"FRcoverage2");
    coverage.addGeneralInterfaceMonitor(MONITOR[3],"FRcoverage3");
    coverage.addGeneralInterfaceMonitor(MONITOR[4],"FRcoverage4");
    coverage.addGeneralInterfaceMonitor(MONITOR[5],"FRcoverage5");
    coverage.addGeneralInterfaceMonitor(MONITOR[6],"FRcoverage6");
    coverage.addGeneralInterfaceMonitor(MONITOR[7],"FRcoverage7");
*/
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
    // V PRIPADE POTREBY ZAPNUT VSETKY POUZITE DRIVERY A MONITORY
    fDriver.setEnabled();
    for(int i=0; i<FLOWS; i++) begin
      fMonitor[i].setEnabled();
      fResponder[i].setEnabled();
      end
    coverage.setEnabled();
  endtask : enableTestEnvironment

  // --------------------------------------------------------------------------
  // Disable test Enviroment
  task disableTestEnvironment();
     // V PRIPADE POTREBY VYPNUT VSETKY POUZITE DRIVERY A MONITORY
     // Disable drivers
    #(1000*CLK_PERIOD);
    fDriver.setDisabled();
    #(12000*CLK_PERIOD);
    for(int i=0; i<FLOWS; i++) begin
      fMonitor[i].setDisabled();
      fResponder[i].setDisabled();
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
     generator.setEnabled(TRANSACTION_COUNT);

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


