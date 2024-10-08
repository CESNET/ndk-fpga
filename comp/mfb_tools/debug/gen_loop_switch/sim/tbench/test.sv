/*
 * file: test.sv
 * brief: Test Cases
 * author: Jan Kubalek <kubalek@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 * date: 2020
 */

import sv_common_pkg::*;
import sv_mvb_pkg::*;
import sv_mfb_pkg::*;
import sv_mi32_pkg::*;
import test_pkg::*;
import math_pkg::*;

program TEST (
    input logic MI_CLK,
    output logic MI_RESET,
    input logic CLK,
    output logic RESET,
    iMi32.tb  MI,
    iMvbRx.tb ETH_RX_MVB,
    iMfbRx.tb ETH_RX_MFB,
    iMfbTx.tb DMA_RX_MFB,
    iMvbTx.tb DMA_RX_MVB,
    iMvbTx.tb ETH_TX_MVB,
    iMfbTx.tb ETH_TX_MFB,
    iMvbRx.tb DMA_TX_MVB,
    iMfbRx.tb DMA_TX_MFB,

    iMvbTx.monitor DMA_RX_MVB_MONITOR,
    iMfbTx.monitor DMA_RX_MFB_MONITOR,
    iMvbTx.monitor ETH_TX_MVB_MONITOR,
    iMfbTx.monitor ETH_TX_MFB_MONITOR
);

    Mi32Transaction mi_blueprint;
    Mi32Driver mi_driver;
    tTransMbx mi_trans_mbx;

    MvbTransaction #(log2(PKT_MTU+1)+log2(RX_DMA_CHANNELS)+HDR_META_WIDTH+1) rx_mvb_blueprint;
    MvbTransaction #(log2(PKT_MTU+1)+log2(TX_DMA_CHANNELS)+HDR_META_WIDTH)   tx_mvb_blueprint;
    MfbTransaction #(ITEM_WIDTH) mfb_blueprint;
    Generator  rx_mvb_generator;
    Generator  rx_mfb_generator;
    //Scoreboard rx_mvb_scoreboard;
    //Scoreboard rx_mfb_scoreboard;
    Generator  tx_mvb_generator;
    Generator  tx_mfb_generator;
    //Scoreboard tx_mvb_scoreboard;
    //Scoreboard tx_mfb_scoreboard;
    MvbDriver    #(REGIONS,log2(PKT_MTU+1)+log2(RX_DMA_CHANNELS)+HDR_META_WIDTH+1) rx_mvb_driver;
    MvbResponder #(REGIONS,log2(PKT_MTU+1)+log2(RX_DMA_CHANNELS)+HDR_META_WIDTH+1) rx_mvb_responder;
    MvbMonitor   #(REGIONS,log2(PKT_MTU+1)+log2(RX_DMA_CHANNELS)+HDR_META_WIDTH+1) rx_mvb_monitor;
    MfbDriver    #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) rx_mfb_driver;
    MfbResponder #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) rx_mfb_responder;
    MfbMonitor   #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) rx_mfb_monitor;
    MvbDriver    #(REGIONS,log2(PKT_MTU+1)+log2(TX_DMA_CHANNELS)+HDR_META_WIDTH) tx_mvb_driver;
    MvbResponder #(REGIONS,log2(PKT_MTU+1)+log2(TX_DMA_CHANNELS)+HDR_META_WIDTH) tx_mvb_responder;
    MvbMonitor   #(REGIONS,log2(PKT_MTU+1)+log2(TX_DMA_CHANNELS)+HDR_META_WIDTH) tx_mvb_monitor;
    MfbDriver    #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) tx_mfb_driver;
    MfbResponder #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) tx_mfb_responder;
    MfbMonitor   #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) tx_mfb_monitor;

    task createGeneratorEnvironment(int packet_size_min, int packet_size_max);
        mi_blueprint = new;

        rx_mvb_generator = new("RX MVB Generator",0);
        rx_mfb_generator = new("RX MFB Generator",0);
        tx_mvb_generator = new("TX MVB Generator",0);
        tx_mfb_generator = new("TX MFB Generator",0);

        rx_mvb_blueprint = new;
        tx_mvb_blueprint = new;
        mfb_blueprint    = new;

        mfb_blueprint.frameSizeMax = packet_size_max;
        mfb_blueprint.frameSizeMin = packet_size_min;

        rx_mvb_generator.blueprint = rx_mvb_blueprint;
        rx_mfb_generator.blueprint =    mfb_blueprint;
        tx_mvb_generator.blueprint = tx_mvb_blueprint;
        tx_mfb_generator.blueprint =    mfb_blueprint;

        mi_trans_mbx = new(1);
    endtask

    task createEnvironment();
        mi_driver = new("MI32 Module",mi_trans_mbx,MI);

        rx_mvb_driver = new("ETH RX MVB Driver",rx_mvb_generator.transMbx,ETH_RX_MVB);
        rx_mfb_driver = new("ETH RX MFB Driver",rx_mfb_generator.transMbx,ETH_RX_MFB);
        tx_mvb_driver = new("DMA TX MVB Driver",tx_mvb_generator.transMbx,DMA_TX_MVB);
        tx_mfb_driver = new("DMA TX MFB Driver",tx_mfb_generator.transMbx,DMA_TX_MFB);

        rx_mvb_monitor = new("DMA RX MVB Monitor",DMA_RX_MVB_MONITOR);
        rx_mfb_monitor = new("DMA RX MFB Monitor",DMA_RX_MFB_MONITOR);
        tx_mvb_monitor = new("ETH TX MVB Monitor",ETH_TX_MVB_MONITOR);
        tx_mfb_monitor = new("ETH TX MFB Monitor",ETH_TX_MFB_MONITOR);

        rx_mvb_responder = new("DMA RX MVB Responder",DMA_RX_MVB);
        rx_mfb_responder = new("DMA RX MFB Responder",DMA_RX_MFB);
        tx_mvb_responder = new("ETH TX MVB Responder",ETH_TX_MVB);
        tx_mfb_responder = new("ETH TX MFB Responder",ETH_TX_MFB);

        rx_mvb_responder.wordDelayEnable_wt = 1;
        rx_mfb_responder.wordDelayEnable_wt = 1;
        tx_mvb_responder.wordDelayEnable_wt = 1;
        tx_mfb_responder.wordDelayEnable_wt = 1;

        rx_mvb_responder.wordDelayDisable_wt = 29;
        rx_mfb_responder.wordDelayDisable_wt = 29;
        tx_mvb_responder.wordDelayDisable_wt = 29;
        tx_mfb_responder.wordDelayDisable_wt = 29;

        //rx_mvb_scoreboard = new(VERBOSE_LEVEL);
        //rx_mfb_scoreboard = new(VERBOSE_LEVEL);
        //tx_mvb_scoreboard = new(VERBOSE_LEVEL);
        //tx_mfb_scoreboard = new(VERBOSE_LEVEL);
        //
        //rx_mvb_driver.setCallbacks(rx_mvb_scoreboard.driverCbs);
        //rx_mfb_driver.setCallbacks(rx_mfb_scoreboard.driverCbs);
        //tx_mvb_driver.setCallbacks(tx_mvb_scoreboard.driverCbs);
        //tx_mfb_driver.setCallbacks(tx_mfb_scoreboard.driverCbs);
        //
        //rx_mvb_monitor.setCallbacks(rx_mvb_scoreboard.monitorCbs);
        //rx_mfb_monitor.setCallbacks(rx_mfb_scoreboard.monitorCbs);
        //tx_mvb_monitor.setCallbacks(tx_mvb_scoreboard.monitorCbs);
        //tx_mfb_monitor.setCallbacks(tx_mfb_scoreboard.monitorCbs);
    endtask

    task resetDesign();
        RESET    = 1;
        MI_RESET = 1;
        #RESET_TIME;
        RESET    = 0;
        MI_RESET = 0;
    endtask

    task enableTestEnvironment();
        mi_driver.setEnabled();

        rx_mvb_driver.setEnabled();
        rx_mfb_driver.setEnabled();
        tx_mvb_driver.setEnabled();
        tx_mfb_driver.setEnabled();

        rx_mvb_monitor.setEnabled();
        rx_mfb_monitor.setEnabled();
        tx_mvb_monitor.setEnabled();
        tx_mfb_monitor.setEnabled();

        rx_mvb_responder.setEnabled();
        rx_mfb_responder.setEnabled();
        tx_mvb_responder.setEnabled();
        tx_mfb_responder.setEnabled();
    endtask

    task disableTestEnvironment();
        //wait(!rx_mvb_driver.busy && !rx_mfb_driver.busy && !tx_mvb_driver.busy && !tx_mfb_driver.busy);
        //do begin
        //    wait(!rx_mvb_monitor.busy && !rx_mfb_monitor.busy && !tx_mvb_monitor.busy && !tx_mfb_monitor.busy);
        //    fork : StayIdleWait0
        //        wait(rx_mvb_monitor.busy || rx_mfb_monitor.busy || tx_mvb_monitor.busy || tx_mfb_monitor.busy) disable StayIdleWait0;
        //        #(100*CLK_PERIOD) disable StayIdleWait0;
        //    join
        //end while(rx_mvb_monitor.busy || rx_mfb_monitor.busy || tx_mvb_monitor.busy || tx_mfb_monitor.busy);

        mi_driver.setDisabled();

        rx_mvb_driver.setDisabled();
        rx_mfb_driver.setDisabled();
        tx_mvb_driver.setDisabled();
        tx_mfb_driver.setDisabled();

        rx_mvb_monitor.setDisabled();
        rx_mfb_monitor.setDisabled();
        tx_mvb_monitor.setDisabled();
        tx_mfb_monitor.setDisabled();

        rx_mvb_responder.setDisabled();
        rx_mfb_responder.setDisabled();
        tx_mvb_responder.setDisabled();
        tx_mfb_responder.setDisabled();
    endtask


    task test0(int mux_sel);
        static Mi32Transaction mi_trans;
        $cast(mi_trans,mi_blueprint.copy());
        mi_trans.be = '1;
        mi_trans.rw = 1;

        $write("\n\n############ TEST CASE %4b ############\n\n",mux_sel);

        ////////
        // Setup MUXes
        for (int i=0;i<4;i++) begin
            mi_trans.address = 4*i;
            mi_trans.data    = mux_sel>>i;
            $write("addr: %x, data: %x\n",mi_trans.address,mi_trans.data);
            mi_trans_mbx.put(mi_trans.copy());
        end
        ////////

        ////////
        // Start Generators

        // RX
        mi_trans.address = 32'h40+4; // Length
        mi_trans.data    = 64;
        mi_trans_mbx.put(mi_trans.copy());

        mi_trans.address = 32'h40+16; // DST MAC low
        mi_trans.data    = 1;
        mi_trans_mbx.put(mi_trans.copy());

        mi_trans.address = 32'h40+20; // DST MAC high
        mi_trans.data    = 2;
        mi_trans_mbx.put(mi_trans.copy());

        mi_trans.address = 32'h40+24; // SRC MAC low
        mi_trans.data    = 3;
        mi_trans_mbx.put(mi_trans.copy());

        mi_trans.address = 32'h40+28; // SRC MAC high
        mi_trans.data    = 4;
        mi_trans_mbx.put(mi_trans.copy());

        mi_trans.address = 32'h40+0; // Control
        mi_trans.data    = 1;
        mi_trans_mbx.put(mi_trans.copy());
        ////

        // TX
        mi_trans.address = 32'h60+4; // Length
        mi_trans.data    = 64;
        mi_trans_mbx.put(mi_trans.copy());

        mi_trans.address = 32'h60+16; // DST MAC low
        mi_trans.data    = 5;
        mi_trans_mbx.put(mi_trans.copy());

        mi_trans.address = 32'h60+20; // DST MAC high
        mi_trans.data    = 6;
        mi_trans_mbx.put(mi_trans.copy());

        mi_trans.address = 32'h60+24; // SRC MAC low
        mi_trans.data    = 7;
        mi_trans_mbx.put(mi_trans.copy());

        mi_trans.address = 32'h60+28; // SRC MAC high
        mi_trans.data    = 8;
        mi_trans_mbx.put(mi_trans.copy());

        mi_trans.address = 32'h60+0; // Control
        mi_trans.data    = 1;
        mi_trans_mbx.put(mi_trans.copy());
        ////////

        rx_mvb_generator.setEnabled(TRANSACTION_COUNT);
        rx_mfb_generator.setEnabled(TRANSACTION_COUNT);
        tx_mvb_generator.setEnabled(TRANSACTION_COUNT);
        tx_mfb_generator.setEnabled(TRANSACTION_COUNT);

        wait(!rx_mvb_generator.enabled && !rx_mfb_generator.enabled && !tx_mvb_generator.enabled && !tx_mfb_generator.enabled);

        ////////
        // Stop Generators
        mi_trans.address = 32'h40+0; // Control
        mi_trans.data    = 0;
        mi_trans_mbx.put(mi_trans.copy());

        mi_trans.address = 32'h40+0; // Control
        mi_trans.data    = 0;
        mi_trans_mbx.put(mi_trans.copy());
        ////////

        #(CLK_PERIOD*500);

        //rx_mvb_scoreboard.display();
        //rx_mfb_scoreboard.display();
        //tx_mvb_scoreboard.display();
        //tx_mfb_scoreboard.display();
    endtask


    initial begin
        resetDesign();
        createGeneratorEnvironment(FRAME_SIZE_MIN, FRAME_SIZE_MAX);
        createEnvironment();
        enableTestEnvironment();
        for (int i=0;i<2**4;i++)
            test0(i);
        disableTestEnvironment();
        $write("Simulation finished successfully! (This simulation does not contain any data correctness checks.)\n");
        $stop();
    end

endprogram
