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


// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
program TEST (
  input  logic           CLK,
  output logic           RESET,
  iNFifoRx.nfifo_write_tb FW[FLOWS],
  iMemRead.tb             MR
  );

  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------
  // AK MA KOMPONENTA VIAC DRIVEROV ALEBO MONITOROV TREBA ICH NA TOMTO MIESTE DEKLAROVAT A V TASKU
  // CREATEENVIRONMENT INSTANCIOVAT

  // Transaction
  BufferTransaction                                                   buffBlueprint;
  // Generator
  Generator                                                           generator[FLOWS];
  // Driver
  nFifoDriver #(DRIVER0_DATA_WIDTH,DRIVER0_FLOWS,DRIVER0_BLOCK_SIZE,
                 DRIVER0_LUT_MEMORY, 0)                               fDriver[FLOWS];
  // Monitor
  MemMonitorNew #(MONITOR0_DATA_WIDTH,MONITOR0_FLOWS,MONITOR0_BLOCK_SIZE,
                 MONITOR0_LUT_MEMORY, MONITOR0_OUTPUT_REG)
                                                                      fMonitor;
  // Scoreboard
  Scoreboard                                                          scoreboard;
  // Coverage
  Coverage #(DATA_WIDTH,FLOWS,BLOCK_SIZE,LUT_MEMORY,0)                coverage;

  // --------------------------------------------------------------------------
  //                       Creating Environment tasks
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Create Test Environment
  task createEnvironment();
    // Create generator
    for(int i=0; i<FLOWS; i++) begin
      generator[i] = new("Generator", i);
      buffBlueprint = new;
      buffBlueprint.dataSize   = GENERATOR0_DATA_SIZE;
      buffBlueprint.flowCount  = GENERATOR0_FLOW_COUNT;
      generator[i].blueprint = buffBlueprint;
    end;

    // Create scoreboard
    scoreboard = new;

    // Coverage class
    coverage = new();

    // Create and connect driver
    if (FLOWS>0)
    begin
      fDriver[0] = new ("Driver0", 0, generator[0].transMbx, FW[0]);
      coverage.addGeneralInterfaceWrite(FW[0],"FWcoverage0");
    end

    if (FLOWS>1)
    begin
      fDriver[1] = new ("Driver1", 1, generator[1].transMbx, FW[1]);
      coverage.addGeneralInterfaceWrite(FW[1],"FWcoverage1");
    end

    if (FLOWS>2)
    begin
      fDriver[2] = new ("Driver2", 2, generator[2].transMbx, FW[2]);
      coverage.addGeneralInterfaceWrite(FW[2],"FWcoverage2");
      fDriver[3] = new ("Driver3", 3, generator[3].transMbx, FW[3]);
      coverage.addGeneralInterfaceWrite(FW[3],"FWcoverage3");
    end

    if (FLOWS>4)
    begin
      fDriver[4] = new ("Driver4", 4, generator[4].transMbx, FW[4]);
      coverage.addGeneralInterfaceWrite(FW[4],"FWcoverage4");
      fDriver[5] = new ("Driver5", 5, generator[5].transMbx, FW[5]);
      coverage.addGeneralInterfaceWrite(FW[5],"FWcoverage5");
      fDriver[6] = new ("Driver6", 6, generator[6].transMbx, FW[6]);
      coverage.addGeneralInterfaceWrite(FW[6],"FWcoverage6");
      fDriver[7] = new ("Driver7", 7, generator[7].transMbx, FW[7]);
      coverage.addGeneralInterfaceWrite(FW[7],"FWcoverage7");
    end

    for(int i=0; i<FLOWS; i++) begin
       fDriver[i].fwDelayEn_wt             = DRIVER0_DELAYEN_WT;
       fDriver[i].fwDelayDisable_wt        = DRIVER0_DELAYDIS_WT;
       fDriver[i].fwDelayLow               = DRIVER0_DELAYLOW;
       fDriver[i].fwDelayHigh              = DRIVER0_DELAYHIGH;
       fDriver[i].setCallbacks(scoreboard.driverCbs);
    end;

    // Create and connect monitor
    fMonitor = new ("Monitor", MR);
      fMonitor.readDelayEn_wt               = MONITOR0_DELAYEN_WT;
      fMonitor.readDelayDisable_wt          = MONITOR0_DELAYDIS_WT;
      fMonitor.pipeDelayEn_wt               = MONITOR0_PIPEEN_WT;
      fMonitor.pipeDelayDisable_wt          = MONITOR0_PIPEDIS_WT;
    fMonitor.setCallbacks(scoreboard.monitorCbs);
    coverage.addGeneralInterfaceMonitor(MR,"MRcoverage");

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
    for(int i=0; i<FLOWS; i++)
        fDriver[i].setEnabled();
    fMonitor.setEnabled();
    coverage.setEnabled();
  endtask : enableTestEnvironment

  // --------------------------------------------------------------------------
  // Disable test Enviroment
  task disableTestEnvironment();
     // V PRIPADE POTREBY VYPNUT VSETKY POUZITE DRIVERY A MONITORY
     // Disable drivers
    #(1000*CLK_PERIOD);
    for(int i=0; i<FLOWS; i++)
        fDriver[i].setDisabled();
    fMonitor.setDisabled();
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
     for(int i=0; i<FLOWS; i++) begin
        generator[i].setEnabled(TRANSACTION_COUNT);
     end

     // Pokud je generator aktivni nic nedelej
    for(int i=0; i<FLOWS; i++) begin
    while (generator[i].enabled)
      #(CLK_PERIOD);
    end

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


