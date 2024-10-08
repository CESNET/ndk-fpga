// test.sv: Automatic test
// Copyright (C) 2023 CESNET z. s. p. o.
// Author: Tomas Fukac <fukac@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

import sv_common_pkg::*;
import sv_mvb_pkg::*;
import sv_wb_pkg::*;
import test_pkg::*;

program TEST (
    input logic    CLK,
    output logic   RESET,
    iWbRx.tb       WRITE,
    iMvbRx.tb      READ,
    iMvbTx.tb      READ_OUT,
    iMvbRx.tb      MATCH,
    iMvbTx.tb      MATCH_OUT,
    iMvbTx.monitor READ_MONITOR,
    iMvbTx.monitor MATCH_MONITOR
);

    WbTransaction  #(DATA_WIDTH, ADDR_WIDTH, USE_FRAGMENTED_MEM) write_bp;
    MvbTransaction #(ADDR_WIDTH)             read_bp;
    MvbTransaction #(DATA_WIDTH)             match_bp;

    Generator write_gen;
    Generator read_gen;
    Generator match_gen;

    WbDriver  #(DATA_WIDTH, ADDR_WIDTH, USE_FRAGMENTED_MEM) write_driver;
    MvbDriver #(1, ADDR_WIDTH)          read_driver;
    MvbDriver #(MVB_ITEMS, DATA_WIDTH)  match_driver;

    MvbResponder #(1, 2*DATA_WIDTH) read_responder;
    MvbResponder #(MVB_ITEMS, ITEMS+1) match_responder;
    MvbMonitor   #(1, 2*DATA_WIDTH) read_monitor;
    MvbMonitor   #(MVB_ITEMS, ITEMS+1) match_monitor;

    Scoreboard #(DATA_WIDTH, ITEMS, USE_FRAGMENTED_MEM) scoreboard;

    task createGeneratorEnvironment();
        write_gen = new("Write Generator", 0);
        read_gen  = new("Read Generator" , 0);
        match_gen = new("Match Generator", 0);
        write_bp  = new;
        read_bp   = new;
        match_bp  = new;
        write_gen.blueprint = write_bp;
        read_gen.blueprint  = read_bp;
        match_gen.blueprint = match_bp;
    endtask

    task createEnvironment();
        write_driver = new("Write Driver", write_gen.transMbx, WRITE);
        read_driver  = new("Read Driver" , read_gen.transMbx,  READ );
        match_driver = new("Match Driver", match_gen.transMbx, MATCH);

        read_monitor   = new("Read Monitor" , READ_MONITOR );
        match_monitor  = new("Match Monitor", MATCH_MONITOR);
        read_responder = new("Read Responder", READ_OUT);
        read_responder.wordDelayEnable_wt  = 0;
        read_responder.wordDelayDisable_wt = 1;
        match_responder = new("Match Responder", MATCH_OUT);
        match_responder.wordDelayEnable_wt  = 0;
        match_responder.wordDelayDisable_wt = 1;

        scoreboard = new();

        write_driver.setCallbacks(scoreboard.writeDriverCbs);
        read_driver.setCallbacks(scoreboard.readDriverCbs);
        match_driver.setCallbacks(scoreboard.matchDriverCbs);

        read_monitor.setCallbacks(scoreboard.readMonitorCbs);
        match_monitor.setCallbacks(scoreboard.matchMonitorCbs);
    endtask

    task resetDesign();
        RESET=1;
        #RESET_TIME RESET = 0;
    endtask

    task enableTestEnvironment();
        write_driver.setEnabled();
        read_driver.setEnabled();
        match_driver.setEnabled();
        read_responder.setEnabled();
        match_responder.setEnabled();
    endtask

    task disableTestEnvironment();
        wait(!write_driver.busy);
        wait(!read_driver.busy);
        wait(!match_driver.busy);
        do begin
            wait(!read_monitor.busy);
            fork : ReadStayIdleWait
                wait(read_monitor.busy) disable ReadStayIdleWait;
                #(100*CLK_PERIOD)       disable ReadStayIdleWait;
            join
        end while(read_monitor.busy);
        do begin
            wait(!match_monitor.busy);
            fork : MatchStayIdleWait
                wait(match_monitor.busy) disable MatchStayIdleWait;
                #(100*CLK_PERIOD)        disable MatchStayIdleWait;
            join
        end while(match_monitor.busy);
        write_driver.setDisabled();
        read_driver.setDisabled();
        match_driver.setDisabled();
        read_monitor.setDisabled();
        match_monitor.setDisabled();
        read_responder.setDisabled();
        match_responder.setDisabled();
    endtask

    task test1();
        $write("\n\n############ TEST CASE 1 ############\n\n");
        read_monitor.setEnabled();
        match_monitor.setEnabled();
        write_gen.setEnabled(WRITE_COUNT);
        wait(!write_gen.enabled);
        wait(!write_driver.busy);
        #(10*CLK_PERIOD)
        match_gen.setEnabled(MATCH_COUNT);
        wait(!match_gen.enabled);
        wait(!match_driver.busy);
        #(10*CLK_PERIOD)
        if(READ_FROM_TCAM == TRUE) begin
            read_gen.setEnabled(READ_COUNT);
            wait(!read_gen.enabled);
        end
        disableTestEnvironment();
        scoreboard.display();
    endtask

    initial begin
        createGeneratorEnvironment();
        createEnvironment();
        enableTestEnvironment();
        resetDesign();
        test1();
        $write("Verification finished successfully!\n");
        $stop();
    end

endprogram
