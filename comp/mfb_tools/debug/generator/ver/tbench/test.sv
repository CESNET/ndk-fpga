// test.sv
// Copyright (C) 2020 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

import sv_common_pkg::*;
import sv_mfb_pkg::*;
import sv_mi32_pkg::*;
import test_pkg::*;

program TEST (
    input  logic CLK,
    output logic RESET,
    iMfbTx.tb TX,
    iMfbTx.monitor MONITOR,
    iMi32.tb  MI32
);

    MfbResponder #(MFB_REGIONS,MFB_REGION_SIZE,MFB_BLOCK_SIZE,MFB_ITEM_WIDTH) responder;
    MfbMonitor   #(MFB_REGIONS,MFB_REGION_SIZE,MFB_BLOCK_SIZE,MFB_ITEM_WIDTH) monitor;
    Scoreboard                                                                scoreboard;

    task createEnvironment();
        monitor = new("Monitor", MONITOR);
        responder = new("Responder", TX);
        responder.wordDelayEnable_wt  = 1;
        responder.wordDelayDisable_wt = 10;
        responder.wordDelayLow  = 1;
        responder.wordDelayHigh = 150;
        scoreboard = new;
        monitor.setCallbacks(scoreboard.monitorCbs);
    endtask

    task resetDesign();
        RESET=1;
        #RESET_TIME
        RESET=0;
    endtask

    task enableTestEnvironment();
        monitor.setEnabled();
        responder.setEnabled();
    endtask

    task disableTestEnvironment();
        do begin
            wait(!monitor.busy);
            fork : StayIdleWait
                wait(monitor.busy) disable StayIdleWait;
                #(100*CLK_PERIOD) disable StayIdleWait;
            join
        end while(monitor.busy);
        monitor.setDisabled();
        responder.setDisabled();
    endtask

    task enableGenerator(int pkt_len, int burst_mode_en, int burst_size);
        Mi32Transaction mi32Transaction ;
        Mi32Driver      mi32Driver      ;
        mi32Transaction = new();
        mi32Driver      = new("Mi32 Driver", null, MI32);

        // Reset packet counter
        mi32Transaction.rw      = 1;
        mi32Transaction.be      = '1;
        mi32Transaction.address = 32'h00;
        mi32Transaction.data    = 32'h10;
        mi32Driver.sendTransaction(mi32Transaction);

        // Setup packet length
        mi32Transaction.rw      = 1;
        mi32Transaction.be      = '1;
        mi32Transaction.address = 32'h04;
        mi32Transaction.data    = pkt_len;
        mi32Driver.sendTransaction(mi32Transaction);

        if (burst_mode_en == 1) begin
            // Set burst size to N packets
            mi32Transaction.rw      = 1;
            mi32Transaction.be      = '1;
            mi32Transaction.address = 32'h08;
            mi32Transaction.data    = {burst_size, 16'h0201};
            mi32Driver.sendTransaction(mi32Transaction);
        end
        else begin
            mi32Transaction.rw      = 1;
            mi32Transaction.be      = '1;
            mi32Transaction.address = 32'h08;
            mi32Transaction.data    = {burst_size, 16'h1};
            mi32Driver.sendTransaction(mi32Transaction);
        end

        // Enable Generator
        mi32Transaction.rw      = 1;
        mi32Transaction.be      = '1;
        mi32Transaction.address = 32'h00;
        mi32Transaction.data    = 32'h1;
        mi32Driver.sendTransaction(mi32Transaction);

        #(10*CLK_PERIOD);
    endtask

    task disableGenerator();
        Mi32Transaction mi32Transaction ;
        Mi32Driver      mi32Driver      ;
        mi32Transaction = new();
        mi32Driver      = new("Mi32 Driver", null, MI32);

        // Disable Generator
        mi32Transaction.rw      = 1;
        mi32Transaction.be      = '1;
        mi32Transaction.address = 32'h00;
        mi32Transaction.data    = 32'h0;
        mi32Driver.sendTransaction(mi32Transaction);

        #(200*CLK_PERIOD);
    endtask

    task checkPktCounter(int burst_mode_en, int burst_size);
        longint sc_pktcnt;
        bit [63:0] pktcnt;

        Mi32Transaction mi32Transaction ;
        Mi32Driver      mi32Driver      ;
        Mi32Monitor     mi32Monitor     ;
        mi32Transaction = new();
        mi32Driver      = new("Mi32 Driver", null, MI32);
        mi32Monitor     = new("Mi32 Monitor", MI32);

        mi32Transaction.data = 32'h0;
        mi32Transaction.rw   = 0;
        mi32Transaction.be   = '1;

        // Read Packet Counter
        // Low part
        mi32Transaction.address = 32'h20;
        mi32Monitor.executeTransaction(mi32Transaction);
        pktcnt[31:0]  = mi32Transaction.data;

        // High part
        mi32Transaction.address = 32'h24;
        mi32Monitor.executeTransaction(mi32Transaction);
        pktcnt[63:32] = mi32Transaction.data;

        #(10*CLK_PERIOD);

        sc_pktcnt = scoreboard.getPktCounter();

        if (burst_mode_en == 1) begin
            if (sc_pktcnt != burst_size) begin
                $write("Mismatch between scoreboard and specified burst size!\n");
                $write("ScoreBoard Counter:\t %10d\n",sc_pktcnt);
                $write("Specified burst:\t\t %10d\n",burst_size);
                $stop();
            end

            if (pktcnt != burst_size) begin
                $write("Mismatch between internal packet counter and specified burst size!\n");
                $write("DUT Counter:\t\t %10d\n",pktcnt);
                $write("Specified burst:\t\t %10d\n",burst_size);
                $stop();
            end
        end

        if (pktcnt != sc_pktcnt) begin
            $write("Mismatch in packet counter!\n");
            $write("ScoreBoard Counter:\t\t %10d\n",sc_pktcnt);
            $write("DUT Counter:\t\t %10d\n",pktcnt);
            $stop();
        end
    endtask

    task wait_burst_to_finish(int length, int burst_mode_en ,int burst_size);
        if (burst_mode_en == 1) begin
            // This is very experimental, but it works. Just provide sufficient
            // time before proceeding further.
            #(100*CLK_PERIOD*burst_size*length);
        end
        else begin
            #(1000*CLK_PERIOD);
        end
    endtask

    task test(int length, int burst_mode_en, int burst_size);
        $write("\n######### Test with packet lenght = %1d (Burst size: %1d, burst mode enabled, %1d) #########\n",length, burst_size, burst_mode_en);
        scoreboard.setPktLen(length);
        enableTestEnvironment();
        enableGenerator(length, burst_mode_en, burst_size);
        wait_burst_to_finish(length, burst_mode_en, burst_size);
        disableGenerator();
        disableTestEnvironment();
        checkPktCounter(burst_mode_en, burst_size);
        scoreboard.display();
    endtask

    initial begin
        // Max burst size the burst mode is tested on
        const int max_bst_size = 10;

        resetDesign();
        createEnvironment();

        // Test with different packet lengths and different burst sizes.
        if (USE_PACP_ARCH != 1'b1) begin
            for (int bst_size = 1; bst_size < max_bst_size; bst_size=bst_size+3) begin
                for (int length = 64; length < 4*MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE; length=length+3) begin
                    test(length, 1, bst_size);
                end
            end
        end

        // Test without burst mode, the packets are sent continuously.
        for (int length = 64; length < 4*MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE; length=length+3) begin
            test(length, 0, 64);
        end

        $write("Verification finished successfully!\n");
        $stop();
    end
endprogram
