/*
 * test.sv: FL_DISCARD_STAT automatic test
 * Copyright (C) 2009 CESNET
 * Author(s): Marek Santa <santa@liberouter.org>
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
import sv_mi32_pkg::*;
import sv_discard_stat_pkg::*;
import test_pkg::*;

// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
program TEST (
  input  logic         CLK,
  output logic         RESET,
  iFrameLinkRx.tb      RX_DRIV[CHANNELS],
  iFrameLinkTx.tb      TX_MUX[CHANNELS],
  iFrameLinkRx.tb      RX_DEMUX[CHANNELS],
  iFrameLinkTx.monitor TX_MON[CHANNELS],
  iFrameLinkRx.tb      RX,
  iFrameLinkTx.tb      TX,
  iMi32.tb             MI,
  iDiscardStat.rx_tb   RX_CHAN,
  iDiscardStat.tx_tb   TX_CHAN,
  iDiscardStat.stat_tb STAT
  );

  // --------------------------------------------------------------------------
  //                       Variables declaration
  // --------------------------------------------------------------------------

  // Transaction
  FrameLinkTransaction                 flBlueprint;
  // Generator
  Generator                            generator[CHANNELS];
  // Driver
  FrameLinkDriver #(DRIVER0_DATA_WIDTH, DRIVER0_DREM_WIDTH) flDriver[CHANNELS];
  // Multiplexor
  FrameLinkMultiplexor #(DRIVER0_DATA_WIDTH, DRIVER0_DREM_WIDTH,
                                  CHANNELS, STATUS_WIDTH)   flMultiplexor;
  // Monitor
  FrameLinkMonitor #(MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH)
                                                           flMonitor[CHANNELS];
  // Demultiplexor
  FrameLinkDemultiplexor #(MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH,
                                  CHANNELS, STATUS_WIDTH)  flDemultiplexor;
  // Discarding Model
  DiscardStatDiscardingModel #(DATA_WIDTH, DREM_WIDTH, CHANNELS,
                                 STATUS_WIDTH, OUTPUT_REG) discardingModel;
  // Scoreboard
  DiscardStatScoreboard #(CHANNELS, TR_TABLE_FIRST_ONLY) scoreboard;
  // Coverage
  Coverage #(DRIVER0_DATA_WIDTH,DRIVER0_DREM_WIDTH,MONITOR0_DATA_WIDTH,MONITOR0_DREM_WIDTH) coverage;

  // Virtual interfaces
  virtual iFrameLinkRx.tb #(DRIVER0_DATA_WIDTH, DRIVER0_DREM_WIDTH)
                                                          vRX_DRIV[CHANNELS];
  virtual iFrameLinkTx.tb #(DRIVER0_DATA_WIDTH, DRIVER0_DREM_WIDTH)
                                                          vTX_MUX[CHANNELS];
  virtual iFrameLinkRx.tb #(MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH)
                                                          vRX_DEMUX[CHANNELS];
  virtual iFrameLinkTx.monitor #(MONITOR0_DATA_WIDTH, MONITOR0_DREM_WIDTH)
                                                          vTX_MON[CHANNELS];
  // --------------------------------------------------------------------------
  //                       Creating Environment tasks
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Create Test Environment
  task createGeneratorEnvironment(int packet_count = GENERATOR0_FL_PACKET_COUNT,
                                  int packet_size_max[] = GENERATOR0_FL_PACKET_SIZE_MAX,
                                  int packet_size_min[] = GENERATOR0_FL_PACKET_SIZE_MIN
                                  );
  // Create generator
    for(int i=0; i<CHANNELS; i++) begin
      string generatorLabel;

      generatorLabel = $sformatf("RX Generator %0d", i);
      generator[i]= new(generatorLabel, i);
      flBlueprint = new;
      flBlueprint.packetCount   = packet_count;
      flBlueprint.packetSizeMax = packet_size_max;
      flBlueprint.packetSizeMin = packet_size_min;
      generator[i].blueprint    = flBlueprint;
    end
  endtask: createGeneratorEnvironment

  task createEnvironment();
    // Assign virtual interfaces
    vRX_DRIV      = RX_DRIV;
    vTX_MUX       = TX_MUX;
    vRX_DEMUX     = RX_DEMUX;
    vTX_MON       = TX_MON;

    // Create scoreboard
    scoreboard = new("Scoreboard");

    // Create discarding model
    discardingModel = new("Discarding Model", RX, RX_CHAN, STAT);
      discardingModel.setCallbacks(scoreboard.driverCbs);

    // Create driver
    for(int i=0; i<CHANNELS; i++) begin
      string driverLabel;

      driverLabel = $sformatf("Driver %0d", i);
      flDriver[i]  = new (driverLabel, generator[i].transMbx, vRX_DRIV[i]);
      flDriver[i].txDelayEn_wt             = DRIVER0_DELAYEN_WT;
      flDriver[i].txDelayDisable_wt        = DRIVER0_DELAYDIS_WT;
      flDriver[i].txDelayLow               = DRIVER0_DELAYLOW;
      flDriver[i].txDelayHigh              = DRIVER0_DELAYHIGH;
      flDriver[i].insideTxDelayEn_wt       = DRIVER0_INSIDE_DELAYEN_WT;
      flDriver[i].insideTxDelayDisable_wt  = DRIVER0_INSIDE_DELAYDIS_WT;
      flDriver[i].insideTxDelayLow         = DRIVER0_INSIDE_DELAYLOW;
      flDriver[i].insideTxDelayHigh        = DRIVER0_INSIDE_DELAYHIGH;
      flDriver[i].setCallbacks(discardingModel.discardStatCbs);
    end

    // Create multiplexor
    flMultiplexor = new ("Multiplexor", vTX_MUX, RX, RX_CHAN);
      flMultiplexor.muxDelayLow            = MULTIPLEXOR_MUXDELAYLOW;
      flMultiplexor.muxDelayHigh           = MULTIPLEXOR_MUXDELAYHIGH;

    // Create monitor
    for(int i=0; i<CHANNELS; i++) begin
      string monitorLabel;

      monitorLabel = $sformatf("Monitor %0d", i);
      flMonitor[i] = new (monitorLabel, vTX_MON[i]);
      flMonitor[i].setCallbacks(scoreboard.monitorCbs);
    end

    // Create demultiplexor
    flDemultiplexor = new ("Demultiplexor", TX, vRX_DEMUX, TX_CHAN);

    // Coverage class
    coverage = new();
      coverage.addFrameLinkInterfaceRx(RX,"RXcoverage");
      coverage.addFrameLinkInterfaceTx(TX,"TXcoverage");
  endtask : createEnvironment

  // --------------------------------------------------------------------------
  //                       Test auxilarity procedures
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Resets design
  task resetDesign();
    #(2*CLK_PERIOD);               // wait before reset
    RESET=1;                       // Init Reset variable
    #RESET_TIME     RESET = 0;     // Deactivate reset after reset_time
  endtask : resetDesign

  // --------------------------------------------------------------------------
  // Enable test Environment
  task enableTestEnvironment();
    // Enable Driver, Monitor, Coverage for each port
    for (int i=0; i<CHANNELS; i++)
      flDriver[i].setEnabled();

    flMultiplexor.setEnabled();
    flDemultiplexor.setEnabled();
    discardingModel.setEnabled();

    for (int i=0; i<CHANNELS; i++)
      flMonitor[i].setEnabled();

    coverage.setEnabled();
  endtask : enableTestEnvironment

  // --------------------------------------------------------------------------
  // Disable test Environment
  task disableTestEnvironment();
    int i;
    bit busy;

    // Check if drivers/monitors are not sending/receiving transaction for
    // 100 CLK_PERIODs
    i = 0;
    while (i<100) begin
      busy = 0;
      for (int j=0; j < CHANNELS; j++)
        if (flMonitor[j].busy || flDriver[j].busy) busy = 1;

      if (busy) i = 0;
      else i++;
      #(CLK_PERIOD);
    end

    // Disable drivers
    for (int i=0; i<CHANNELS; i++)
      flDriver[i].setDisabled();

    flMultiplexor.setDisabled();

    // Disable monitors
    discardingModel.setDisabled();
    flDemultiplexor.setDisabled();

    for (int i=0; i<CHANNELS; i++)
      flMonitor[i].setDisabled();

    coverage.setDisabled();
  endtask : disableTestEnvironment

  // -- Read Frame Counters ---------------------------------------------------
  //! Read Frame Counters
  /*!
   * Function reads values in frame counter registers via MI32.
   */
  task readFrameCounters();
    automatic Mi32Transaction mi32Transaction = new();
    automatic Mi32Driver      mi32Driver      = new("Mi32 Driver", null, MI);
    automatic Mi32Monitor     mi32Monitor     = new("Mi32 Monitor", MI);
    bit [63:0] droppedFrames[CHANNELS];    // Dropped Frames Counter
    bit [63:0] passedFrames[CHANNELS];     // Passed Frames Counter
    bit [63:0] droppedLength[CHANNELS];    // Length of Dropped Frames Counter
    bit [63:0] passedLength[CHANNELS];     // Length of Passed Frames Counter

    mi32Transaction.rw      = 0;
    mi32Transaction.be      = '1;

    for (int i=0; i<CHANNELS; i++) begin
      if (COUNT_DROP) begin
        // Read Dropped Frames Counter
         // Low part
        mi32Transaction.address = 32'h00+8*i;
        mi32Monitor.executeTransaction(mi32Transaction);
        droppedFrames[i][31:0]  = mi32Transaction.data;

         // High part
        mi32Transaction.address = 32'h04+8*i;
        mi32Monitor.executeTransaction(mi32Transaction);
        droppedFrames[i][63:32] = mi32Transaction.data;
      end

      if (COUNT_PASS) begin
        // Read Passed Frames Counter
         // Low part
        mi32Transaction.address = 32'h200+8*i;
        mi32Monitor.executeTransaction(mi32Transaction);
        passedFrames[i][31:0]  = mi32Transaction.data;

         // High part
        mi32Transaction.address = 32'h204+8*i;
        mi32Monitor.executeTransaction(mi32Transaction);
        passedFrames[i][63:32] = mi32Transaction.data;
      end

      if (COUNT_DROP_LEN) begin
        // Read Length of Dropped Frames Counter
         // Low part
        mi32Transaction.address = 32'h400+8*i;
        mi32Monitor.executeTransaction(mi32Transaction);
        droppedLength[i][31:0]  = mi32Transaction.data;

         // High part
        mi32Transaction.address = 32'h404+8*i;
        mi32Monitor.executeTransaction(mi32Transaction);
        droppedLength[i][63:32] = mi32Transaction.data;
      end

      if (COUNT_PASS_LEN) begin
        // Read Length of Passed Frames Counter
         // Low part
        mi32Transaction.address = 32'h600+8*i;
        mi32Monitor.executeTransaction(mi32Transaction);
        passedLength[i][31:0]  = mi32Transaction.data;

         // High part
        mi32Transaction.address = 32'h604+8*i;
        mi32Monitor.executeTransaction(mi32Transaction);
        passedLength[i][63:32] = mi32Transaction.data;
      end

      // Display counters values
      $write("------------------------------------------------------------\n");
      $write("-- Channel %0d Frame Counters\n", i);
      $write("------------------------------------------------------------\n");
      if (COUNT_DROP)
        $write("Dropped Frames Counter:\t\t %10d\n",droppedFrames[i]);
      if (COUNT_PASS)
        $write("Passed Frames Counter:\t\t %10d\n",passedFrames[i]);
      if (COUNT_DROP_LEN)
        $write("Length of Dropped Frames Counter:\t %10d\n",droppedLength[i]);
      if (COUNT_PASS_LEN)
        $write("Length of Passed Frames Counter:\t %10d\n",passedLength[i]);
      $write("------------------------------------------------------------\n");
    end

    // Check frame counters
    checkFrameCounters(droppedFrames,passedFrames,droppedLength,passedLength);
    #(20*CLK_PERIOD);

  endtask : readFrameCounters

  // -- Check Frame Counters --------------------------------------------------
  //! Check Frame Counters
  /*!
   * Function check values of frame counters.
   */
  function void checkFrameCounters(bit [63:0] droppedFrames[CHANNELS],
                                   bit [63:0] passedFrames[CHANNELS],
                                   bit [63:0] droppedLength[CHANNELS],
                                   bit [63:0] passedLength[CHANNELS]
                                   );
    longint unsigned droppedFr[CHANNELS];   // Dropped Frames Counter
    longint unsigned passedFr[CHANNELS];    // Passed Frames Counter
    longint unsigned droppedLen[CHANNELS];  // Length of Dropped Frames Counter
    longint unsigned passedLen[CHANNELS];   // Length of Passed Frames Counter

    discardingModel.getStats(droppedFr, passedFr, droppedLen, passedLen);

    for (int i=0; i<CHANNELS; i++) begin
      if ((COUNT_DROP && droppedFrames[i] != droppedFr[i]) ||
          (COUNT_PASS && passedFrames[i] != passedFr[i]) ||
          (COUNT_DROP_LEN && droppedLength[i] != droppedLen[i]) ||
          (COUNT_PASS_LEN && passedLength[i] != passedLen[i])) begin
        // Display counters values
        $write("------------------------------------------------------------\n");
        $write("-- Channel %0d Frame Counters mismatch\n", i);
        $write("------------------------------------------------------------\n");
        if (COUNT_DROP && droppedFrames[i] != droppedFr[i])
          $write("Dropped Frames does not match! Expected:%10d, Received:%10d\n",
                  droppedFr[i], droppedFrames[i]);
        if (COUNT_PASS && passedFrames[i] != passedFr[i])
          $write("Passed Frames does not match! Expected:%10d, Received:%10d\n",
                  passedFr[i], passedFrames[i]);
        if (COUNT_DROP_LEN && droppedLength[i] != droppedLen[i])
          $write("Dropped Length does not match! Expected:%10d, Received:%10d\n",
                  droppedLen[i], droppedLength[i]);
        if (COUNT_PASS_LEN && passedLength[i] != passedLen[i])
          $write("Passed Length does not match! Expected:%10d, Received:%10d\n",
                  passedLen[i], passedLength[i]);
        $write("------------------------------------------------------------\n");
      end
    end

  endfunction : checkFrameCounters

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
     for (int i=0; i<CHANNELS; i++)
       generator[i].setEnabled(TRANSACTION_COUNT);

     // wait until generator is disabled
     for (int i=0; i<CHANNELS; i++)
       wait (generator[i].enabled == 0);

     // Disable Test Enviroment
     disableTestEnvironment();

     // Display Scoreboard
     scoreboard.display();
     coverage.display();

     // Read frames counters
     readFrameCounters();
  endtask: test1


  // --------------------------------------------------------------------------
  //                           Main test part
  // --------------------------------------------------------------------------
  initial begin
    // Set RNG seed
//    process proc;
//    proc = process::self();
//    proc.srandom(RNG_SEED);

    // -------------------------------------
    // DESIGN ENVIROMENT
    // -------------------------------------
    resetDesign(); // Reset design
    // Wait while component is ready to receive
    wait (RX_CHAN.rx_cb.DST_RDY_N == '0);

    createGeneratorEnvironment();
    createEnvironment(); // Create Test Enviroment
    // -------------------------------------
    // TESTING
    // -------------------------------------
    $write("\n\n############ GENERICS ############\n\n");
    $write("DATA_WIDTH:\t%0d\nCHANNELS:\t%0d\nSTATUS_WIDTH:\t%0d\nCNT_WIDTH:\t%0d\n",DATA_WIDTH,CHANNELS,STATUS_WIDTH,CNT_WIDTH);

    test1();       // Run Test 1

    // -------------------------------------
    // STOP TESTING
    // -------------------------------------
    $write("Verification finished successfully!\n");
    $stop();       // Stop testing
  end

endprogram

