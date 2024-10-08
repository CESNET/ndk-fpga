// crossbarx_stream.vhd: Crossbarx stream
// Copyright (C) 2020 CESNET z. s. p. o.
// Author(s): Daniel Kriz <xkrizd01@vutbr.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

import sv_common_pkg::*;
import sv_mfb_pkg::*;
import test_pkg::*;
// New transaction which rewrites metadata (Discard) to 0 or 1
class myTransaction extends MfbTransaction #(MFB_ITEM_WIDTH,EXT_META_WIDTH);
    function  void post_randomize ();
        if(DISCARD == 0) begin
            meta[0 : 0] = '0; // discard is disabled
        end else begin
            meta[0 : 0] = '1; // discard is always asserted
        end
    endfunction
    virtual function Transaction copy(Transaction to = null);
        myTransaction tr;
        if (to == null) begin
            tr = new;
        end else begin
            $cast(tr, to);
        end
        super.copy(tr);
        return tr;
    endfunction
endclass
program TEST (
    input logic  RX_CLK,
    input logic  RX_CLK2,
    input logic  TX_CLK,
    input logic  CX_CLK_ARB,
    output logic ASYNC_RESET,
    iMfbRx.tb RX,
    iMfbTx.tb TX,
    iMfbTx.monitor MONITOR
);

    MfbTransaction #(MFB_ITEM_WIDTH,EXT_META_WIDTH) blueprint;
    myTransaction my_blueprint;
    Generator generator;
    MfbDriver #(MFB_REGIONS,MFB_REGION_SIZE,MFB_BLOCK_SIZE,MFB_ITEM_WIDTH,0,EXT_META_WIDTH,1) mfb_driver;
    MfbResponder #(MFB_REGIONS,MFB_REGION_SIZE,MFB_BLOCK_SIZE,MFB_ITEM_WIDTH,MFB_META_WIDTH,1) mfb_responder;
    MfbMonitor #(MFB_REGIONS,MFB_REGION_SIZE,MFB_BLOCK_SIZE,MFB_ITEM_WIDTH,MFB_META_WIDTH,1) mfb_monitor;
    mfb_speed #(mfb_speed_cbs_rx #(MFB_ITEM_WIDTH,EXT_META_WIDTH)) mfb_speed_rx;
    mfb_speed #(mfb_speed_cbs_tx #(MFB_ITEM_WIDTH,MFB_META_WIDTH)) mfb_speed_tx;
    Scoreboard scoreboard;

    task createGeneratorEnvironment(int packet_size_max, int packet_size_min);
        generator = new("Generator", 0);
        // When DISCARD = 1 then the original transaction where Discards are randomly generated is used
        // Otherwise, transaction with rewritten metadata is used
        if(DISCARD == 1) begin
            blueprint = new;
            blueprint.frameSizeMax = packet_size_max;
            blueprint.frameSizeMin = packet_size_min;
            generator.blueprint = blueprint;
        end else begin
            my_blueprint = new;
            my_blueprint.frameSizeMax = packet_size_max;
            my_blueprint.frameSizeMin = packet_size_min;
            generator.blueprint = my_blueprint;
        end
    endtask

    task createEnvironment();
        mfb_driver  = new ("Driver", generator.transMbx, RX);
        mfb_monitor = new ("Monitor", MONITOR);
        mfb_responder = new ("Responder", TX);

        mfb_speed_rx = new("MFB RX");
        mfb_speed_rx.delay = RX_MFB_SPEED_DELAY;
        mfb_speed_tx = new("MFB TX");
        mfb_speed_tx.delay = TX_MFB_SPEED_DELAY;

        mfb_monitor.gap_size_check = F_GAP_ADJUST_EN;
        mfb_monitor.ref_gap_size_min = F_GAP_ADJUST_SIZE_MIN;
        mfb_monitor.ref_gap_size_avg = F_GAP_ADJUST_SIZE_AVG;

        // Chance of src ready fall and rise
        mfb_driver.wordDelayEnable_wt  =     SRC_RDY_OFF_CHANCE;
        mfb_driver.wordDelayDisable_wt = 100-SRC_RDY_OFF_CHANCE;

        mfb_driver.wordDelayHigh = SRC_RDY_OFF_TIME_MAX;
        mfb_driver.wordDelayLow  = SRC_RDY_ON_TIME_MAX;

        // Chance of dst ready fall and rise
        mfb_responder.wordDelayEnable_wt  =     DST_RDY_OFF_CHANCE;
        mfb_responder.wordDelayDisable_wt = 100-DST_RDY_OFF_CHANCE;

        mfb_responder.wordDelayHigh = DST_RDY_OFF_TIME_MAX;
        mfb_responder.wordDelayLow  = DST_RDY_ON_TIME_MAX;

        scoreboard = new;
        mfb_driver.setCallbacks(scoreboard.driverCbs);
        mfb_monitor.setCallbacks(scoreboard.monitorCbs);

        mfb_driver.setCallbacks(mfb_speed_rx.cbs);
        mfb_monitor.setCallbacks(mfb_speed_tx.cbs);
    endtask

    task resetDesign();
        ASYNC_RESET = 1;
        #RESET_TIME
        ASYNC_RESET = 0;
    endtask

    task enableTestEnvironment();
        mfb_driver.setEnabled();
        mfb_monitor.setEnabled();
        mfb_responder.setEnabled();
        if(THROUGHPUT_MEAS_EN == 1) begin
            mfb_speed_rx.setEnabled();
            mfb_speed_tx.setEnabled();
        end
    endtask

    task disableTestEnvironment();
        wait (!mfb_driver.busy);
        do begin
            wait (!mfb_monitor.busy);
            fork : StayIdleWait
                wait (mfb_monitor.busy) disable StayIdleWait;
                #(1000*RX_CLK_PERIOD) disable StayIdleWait;
            join
        end while (mfb_monitor.busy);
        mfb_driver.setDisabled();
        mfb_responder.setDisabled();
        if(THROUGHPUT_MEAS_EN == 1) begin
            wait(mfb_speed_tx.speed == 0);
            mfb_speed_rx.setDisabled();
            mfb_speed_tx.setDisabled();
        end

        mfb_monitor.setDisabled();
    endtask

    task test1();
        $write("\n\n############ TEST CASE 1 ############\n\n");
        enableTestEnvironment();
        generator.setEnabled(TRANSACTION_COUNT);
        wait (!generator.enabled);
        disableTestEnvironment();
        scoreboard.display();
    endtask

    initial begin
        resetDesign();
        createGeneratorEnvironment(FRAME_SIZE_MAX, FRAME_SIZE_MIN);
        createEnvironment();
        test1();
        $write("Verification finished successfully!\n");
        $stop();
    end

endprogram
