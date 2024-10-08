/*
 * test.sv: Automatic DUT test
 * Copyright (C) 2018 CESNET
 * Author(s): Lukas Kekely <kekely@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

import dpi_sw_access::*;
import sv_common_pkg::*;
import sv_flu_pkg::*;
import test_pkg::*;



program TEST (
  input  logic CLK,
  output logic RESET,
  iFrameLinkUTx.tb TX,
  iFrameLinkUTx.monitor MONITOR,
  iMi32.tb MI
);

  FrameLinkUMonitor #(DATA_WIDTH, EOP_POS_WIDTH, SOP_POS_WIDTH)    fluMonitor;
  FrameLinkUResponder #(DATA_WIDTH, EOP_POS_WIDTH, SOP_POS_WIDTH)  fluResponder;
  Scoreboard scoreboard;

  task createEnvironment();
    dpiconnect(0, MI);
    fluMonitor = new ("Monitor", MONITOR);
    fluResponder = new ("Responder", TX);
    fluResponder.rxDelayEn_wt            = 1;
    fluResponder.rxDelayDisable_wt       = 49;
    fluResponder.rxDelayLow              = 1;
    fluResponder.rxDelayHigh             = 3;
    fluResponder.insideRxDelayEn_wt      = 0;
    fluResponder.insideRxDelayDisable_wt = 1;
    scoreboard = new;
    fluMonitor.setCallbacks(scoreboard.monitorCbs);
  endtask

  task resetDesign();
    RESET=1;
    #RESET_TIME RESET = 0;
  endtask

  task enableTestEnvironment();
    fluMonitor.setEnabled();
    fluResponder.setEnabled();
    dpiwait(0, 1);
  endtask

  task disableTestEnvironment();
    fluMonitor.setDisabled();
    fluResponder.setDisabled();
  endtask

  task test(int length);
    $write("\n\n############ TEST %0d B ############\n", length);
    dpiwrite(0, 4, length);
    scoreboard.init(length);
    dpiwrite(0, 0, 1);
    dpiwait(0, GENERATOR_WAIT);
    dpiwrite(0, 0, 0);
    dpiwait(0, IDLE_WAIT);
    scoreboard.display();
  endtask

  // --------------------------------------------------------------------------
  //                           Main test part
  // --------------------------------------------------------------------------
  initial begin
    resetDesign();
    createEnvironment();
    enableTestEnvironment();
    //for(int i=0; i<LENGTHS.size; i++)
    //  test(LENGTHS[i]);
    for(int i=60; i<1024; i++)
      test(i);
    disableTestEnvironment();
    $write("Verification finished successfully!\n");
    $stop();
  end

endprogram

