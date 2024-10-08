//-- test.sv: Test Cases.
//-- Copyright (C) 2020 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause
// -- TODO: Implement a check of the order in which packets arrive in the DUT and in which packets exit the DUT of the TX/RX_STREAMS interfaces (make callbacks array of TX/RX_STREAMSinterfaces and assign to one set of callback one scoreboard).
// -- This guarantees the control order in which packets arrives on individual streams.

import sv_mvb_pkg::*;
import test_pkg::*;
import sv_common_pkg::*;



program TEST (
    input logic     CLK,
    output logic    RESET,
    iMvbRx.tb       RX_STREAMS[NUMBER_OF_STREAMS],
    iMvbTx.tb       TX_STREAMS[NUMBER_OF_STREAMS],
    iMvbTx.tb       TX_GLOBAL,
    iMvbTx.monitor  TX_STREAMS_MONITOR[NUMBER_OF_STREAMS],
    iMvbTx.monitor  TX_GLOBAL_MONITOR,
    iPtr.tb         PTR_INT
);

    Scoreboard scoreboard;

    // -- Array of virtual interface divided by streams
    virtual iMvbRx #(NUMBER_OF_PACKETS,RX_ITEM_WIDTH).tb        vRX_STREAMS [NUMBER_OF_STREAMS];
    virtual iMvbTx #(NUMBER_OF_PACKETS,TX_ITEM_WIDTH).tb        vTX_STREAMS [NUMBER_OF_STREAMS];

    // -- Array of virtual interface monitors
    virtual iMvbTx #(NUMBER_OF_PACKETS,TX_ITEM_WIDTH).monitor   vTX_STREAMS_MONITOR [NUMBER_OF_STREAMS];

    // -- Generators for packters (one generator for each stream interface)
    Generator  packetGenerator[NUMBER_OF_STREAMS];
    MvbTransaction #(RX_ITEM_WIDTH) blueprint;

    // -- Drivers for input interfaces (one driver for each interface)
    MvbDriver #(NUMBER_OF_PACKETS,RX_ITEM_WIDTH)  streamsDrivers[NUMBER_OF_STREAMS];
    // -- Monitors and responders for streams output interfaces (one driver and responder for one interface. one interface is one stream)
    MvbMonitor #(NUMBER_OF_PACKETS,TX_ITEM_WIDTH) streamsMonitors[NUMBER_OF_STREAMS];
    MvbResponder #(NUMBER_OF_PACKETS,TX_ITEM_WIDTH) streamResponder[NUMBER_OF_STREAMS];

    // -- Monitor and responder for global output interface (all stream interfaces are combinated into this one interface)
    MvbMonitor #(TX_GLOBAL_ITEMS,TX_GLOBAL_ITEM_WIDTH) globalMonitor;
    MvbResponder #(TX_GLOBAL_ITEMS,TX_GLOBAL_ITEM_WIDTH) globalResponder;

    task createEnvironment();
        vRX_STREAMS=RX_STREAMS;
        vTX_STREAMS_MONITOR=TX_STREAMS_MONITOR;
        vTX_STREAMS=TX_STREAMS;
        // -- Creating generators
        blueprint=new;
        foreach (packetGenerator[i]) begin
            packetGenerator[i] = new("Generator", 0);
            packetGenerator[i].blueprint = blueprint;
        end
        // -- Creating drivers
        foreach(streamsDrivers[i])begin
            streamsDrivers[i] = new("Driver", packetGenerator[i].transMbx, vRX_STREAMS[i]);
        end
        // -- Creating monitors
        foreach(streamsMonitors[i])begin
            streamsMonitors[i] = new("Monitor", vTX_STREAMS_MONITOR[i]);
        end
        globalMonitor = new("Global monitor", TX_GLOBAL_MONITOR);
        // -- Creating responders
        foreach(streamResponder[i])begin
            streamResponder[i] = new("Responder", vTX_STREAMS[i]);
            streamResponder[i].wordDelayEnable_wt = STREAM_OUTPUT_AFULL ?  0 : 20;
        end
        globalResponder = new("Global responder", TX_GLOBAL);
        globalResponder.wordDelayEnable_wt  =  GLOBAL_OUTPUT_AFULL ? 0 : 10;

        scoreboard=new(PTR_INT);
        // -- Set up callbacks
        foreach(streamsDrivers[i])begin
            streamsDrivers[i].setCallbacks(scoreboard.streamDriverCbs);
        end
        foreach(streamsMonitors[i])begin
            streamsMonitors[i].setCallbacks(scoreboard.streamMonitorCbs);
        end
        globalMonitor.setCallbacks(scoreboard.globalMonitorCbs);
    endtask

    task resetDesign();
        RESET=1;
        #RESET_TIME RESET = 0;
    endtask

    task enableTestEnvironment();
        // -- Enabling drivers
        foreach(streamsDrivers[i])begin
            streamsDrivers[i].setEnabled();
        end
        // -- Enabling responders
        foreach(streamResponder[i])begin
            streamResponder[i].setEnabled();
        end
        globalResponder.setEnabled();
        // -- Enabling process dedicated for moving SPACE_GLB pointer
        scoreboard.ptrMov.setEnabled();
    endtask

    task disableTestEnvironment();
        // -- Waiting for generators to stop their actions
        foreach(packetGenerator[i])begin
            wait(!packetGenerator[i].enabled);
        end
        // -- Waiting for DUT to finish the process
        scoreboard.wait_for();
        // -- Disabling process
        scoreboard.ptrMov.setDisabled();
        // -- Disabling drivers
        foreach(streamsDrivers[i])begin
            streamsDrivers[i].setDisabled();
        end
        // -- Disabling monitors
        foreach(streamsMonitors[i])begin
            streamsMonitors[i].setDisabled();
        end
        globalMonitor.setDisabled();
        // -- Disabling responders
        foreach(streamResponder[i])begin
            streamResponder[i].setDisabled();
        end
        globalResponder.setDisabled();
    endtask


    task test1();
        $write("\n\n############ TEST CASE 1 ############\n\n");
        // -- Enabling monitors
        foreach(streamsMonitors[i])begin
            streamsMonitors[i].setEnabled();
        end
        globalMonitor.setEnabled();
        // -- Enable all generators (one generator have to generate TRANSACTION_COUNT/NUMBER_OF_STREAMS of transactions)
        foreach(packetGenerator[i])begin
            packetGenerator[i].setEnabled(TRANSACTION_COUNT/NUMBER_OF_STREAMS);
        end

        disableTestEnvironment();
        scoreboard.display();
    endtask

    initial begin
        createEnvironment();
        enableTestEnvironment();
        resetDesign();
        test1();

        $write("Verification finished successfully!\n");
        $stop();
    end

endprogram
