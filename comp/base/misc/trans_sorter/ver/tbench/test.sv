//-- test.sv: Test Cases.
//-- Copyright (C) 2020 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import sv_common_pkg::*;
import sv_mvb_pkg::*;
import test_pkg::*;

program TEST (
    input logic     CLK,
    output logic    RESET,
    iAFull.tb       FIFO_AFULL,
    iMvbRx.tb       RX_TRANS,
    iMvbTx.monitor  RX_TRANS_MONITOR,
    iMvbTx.tb       TX_TRANS,
    iMvbTx.monitor  TX_TRANS_MONITOR,
    iMvbRx.tb       RX_CONFS,
    iMvbTx.monitor  RX_CONFS_MONITOR
);

    tTransMbx       confsMbx;

    MvbTransaction  #(META_WIDTH) transBlueprint;
    Generator       rxTransGenerator;

    MvbDriver       #(MAX_RX_TRANS,ITEM_WIDTH)  rxTransDriver;
    MvbMonitor      #(MAX_RX_TRANS,ITEM_WIDTH)  rxTransMonitor;

    MvbDriver       #(MAX_ID_CONFS,ID_WIDTH)    rxConfsDriver;
    MvbMonitor      #(MAX_ID_CONFS,ID_WIDTH)    rxConfsMonitor;

    MvbMonitor      #(MAX_TX_TRANS,ITEM_WIDTH)  txTransMonitor;
    MvbResponder    #(MAX_TX_TRANS,ITEM_WIDTH)  txTransResponder;

    Scoreboard      scoreboard;

    task createEnvironment();
        //  Creating mailbox for confirmations.
        confsMbx=new(1);

        //  Creating generator and assigning blueprint that the generator will use.
        rxTransGenerator = new("Transaction generator", 0);
        transBlueprint = new;
        rxTransGenerator.blueprint = transBlueprint;

        //  Creating of infrastructure for RX interfaces.
        rxTransMonitor = new("Transaction monitor", RX_TRANS_MONITOR);
        rxTransDriver  = new("Transaction driver", rxTransGenerator.transMbx, RX_TRANS);
        rxConfsMonitor = new("Confirmation monitor", RX_CONFS_MONITOR);
        rxConfsDriver  = new("Confirmation driver", confsMbx, RX_CONFS);

        //  Creating of infrastructure for TX interfaces.
        txTransMonitor = new("Monitor", TX_TRANS_MONITOR);
        txTransResponder = new("Transaction responder", TX_TRANS);

        scoreboard = new(confsMbx,FIFO_AFULL);

        rxTransMonitor.setCallbacks(scoreboard.rxTransMonitorCbs);
        rxTransDriver.setCallbacks(scoreboard.rxTransDriverCbs);
        rxConfsMonitor.setCallbacks(scoreboard.rxConfsMonitorCbs);
        txTransMonitor.setCallbacks(scoreboard.txTransMonitorCbs);
    endtask

    task resetDesign();
        RESET=1;
        #RESET_TIME RESET = 0;
    endtask

    //  Enabling every verification component.
    task enableTestEnvironment();
        rxTransDriver.setEnabled();
        rxConfsDriver.setEnabled();
        txTransMonitor.setEnabled();
        rxTransMonitor.setEnabled();
        rxConfsMonitor.setEnabled();
        txTransResponder.setEnabled();
        //  Enabling of Confirmator.
        scoreboard.setEnabled();
        //  Setting up number of transactions that will be generated.
        rxTransGenerator.setEnabled(TRANSACTION_COUNT);
    endtask

    // This task manage that there is not any active verification component
    // (Driver, Generator....) and no more transaction are transfered.
    task disableTestEnvironment();
        scoreboard.setDisabled();
        //  Waiting for both drivers to end their actions.
        wait(!rxTransDriver.busy||!rxConfsDriver.busy);
        //  Waiting for monitor to end its actions.
        do begin
            wait(!txTransMonitor.busy);
            fork : StayIdleWait
                wait(txTransMonitor.busy) disable StayIdleWait;
                #(100*CLK_PERIOD) disable StayIdleWait;
            join
        end while(txTransMonitor.busy);
        //  Waiting for rxTransMonitor to end its actions.
        do begin
            wait(!rxTransMonitor.busy);
            fork : StayIdleWaitTrans
                wait(rxTransMonitor.busy) disable StayIdleWaitTrans;
                #(100*CLK_PERIOD) disable StayIdleWaitTrans;
            join
        end while(rxTransMonitor.busy);
        //  Waiting for rxConfsMonitor to end its actions.
        do begin
            wait(!rxConfsMonitor.busy);
            fork : StayIdleWaitConfs
                wait(rxConfsMonitor.busy) disable StayIdleWaitConfs;
                #(100*CLK_PERIOD) disable StayIdleWaitConfs;
            join
        end while(rxConfsMonitor.busy);
        //  Disabling every verification component.
        rxTransDriver.setDisabled();
        rxConfsDriver.setDisabled();
        txTransMonitor.setDisabled();
        rxTransMonitor.setDisabled();
        rxConfsMonitor.setDisabled();
        txTransResponder.setDisabled();
    endtask

    task test1();
        $write("\n\n-- TEST CASE 1 -----------------------------------------\n\n");
        //  Set up of the verification environment constraints.
        txTransResponder.wordDelayEnable_wt = 2;
        txTransResponder.wordDelayDisable_wt = 8;
        enableTestEnvironment();

        #(20*CLK_PERIOD);
        //  Waiting for generator to end generating.
        wait(rxTransGenerator.enabled==0);
        //  Waiting predetermined time.
        #(TIME_TO_WAIT_AFTER_GENERATOR_FINISHED*CLK_PERIOD);

        disableTestEnvironment();
        //  Displaying scoreboard.
        scoreboard.display();
        $write("-- End of TEST CASE 1 --------------------------------------\n\n");
        $write("------------------------------------------------------------\n");
    endtask

    task test2();
        $write("\n\n-- TEST CASE 2 -----------------------------------------\n\n");
        //  Set up of the verification environment constraints.
        txTransResponder.wordDelayEnable_wt = 8;
        txTransResponder.wordDelayDisable_wt = 2;
        enableTestEnvironment();

        #(20*CLK_PERIOD);

        //  Waiting for generator to end generating.
        wait(rxTransGenerator.enabled==0);
        //  Waiting predetermined time.
        #(TIME_TO_WAIT_AFTER_GENERATOR_FINISHED*CLK_PERIOD);

        disableTestEnvironment();
        //  Displaying scoreboard.
        scoreboard.display();
        $write("-- End of TEST CASE 2 --------------------------------------\n\n");
        $write("------------------------------------------------------------\n");
    endtask

    initial begin
        resetDesign();
        createEnvironment();
        test1();

        resetDesign();
        createEnvironment();
        test2();

        $write("------------------------------------------------------------\n");
        $write("-- Verification finished successfully!\n");
        $write("------------------------------------------------------------\n");
        $stop();
    end

endprogram
