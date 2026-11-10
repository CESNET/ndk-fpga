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
        Mi32Monitor     mi32Monitor     ;
        mi32Transaction = new();
        mi32Driver      = new("Mi32 Driver", null, MI32);
        mi32Monitor     = new("Mi32 Monitor", MI32);

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

        // sync read
        mi32Transaction.rw      = 0;
        mi32Transaction.address = 32'h00;
        mi32Monitor.executeTransaction(mi32Transaction);

        #(5*CLK_PERIOD);
    endtask

    task disableGenerator();
        Mi32Transaction mi32Transaction ;
        Mi32Driver      mi32Driver      ;
        Mi32Monitor     mi32Monitor     ;
        mi32Transaction = new();
        mi32Driver      = new("Mi32 Driver", null, MI32);
        mi32Monitor     = new("Mi32 Monitor", MI32);

        // Disable Generator
        mi32Transaction.rw      = 1;
        mi32Transaction.be      = '1;
        mi32Transaction.address = 32'h00;
        mi32Transaction.data    = 32'h0;
        mi32Driver.sendTransaction(mi32Transaction);

        // sync read
        mi32Transaction.rw      = 0;
        mi32Transaction.address = 32'h00;
        mi32Monitor.executeTransaction(mi32Transaction);

        #(50*CLK_PERIOD);
    endtask

    // Writes the SRC IP mask and the flow control register. The first write of the
    // flow control register keeps per_pkt = 0, so the packet index starts from 0.
    task setFlow(bit [31:0] flow_ctrl, bit [31:0] src_ip_mask);
        Mi32Transaction mi32Transaction ;
        Mi32Driver      mi32Driver      ;
        Mi32Monitor     mi32Monitor     ;
        mi32Transaction = new();
        mi32Driver      = new("Mi32 Driver", null, MI32);
        mi32Monitor     = new("Mi32 Monitor", MI32);

        mi32Transaction.rw      = 1;
        mi32Transaction.be      = '1;
        mi32Transaction.address = 32'h28;
        mi32Transaction.data    = src_ip_mask;
        mi32Driver.sendTransaction(mi32Transaction);

        mi32Transaction.address = 32'h2C;
        mi32Transaction.data    = flow_ctrl & ~32'h1;
        mi32Driver.sendTransaction(mi32Transaction);

        mi32Transaction.data    = flow_ctrl;
        mi32Driver.sendTransaction(mi32Transaction);

        // sync read
        mi32Transaction.rw      = 0;
        mi32Transaction.address = 32'h2C;
        mi32Monitor.executeTransaction(mi32Transaction);
        if (mi32Transaction.data != flow_ctrl) begin
            $write("Flow control register is 0x%08h, expected 0x%08h\n", mi32Transaction.data, flow_ctrl);
            $stop();
        end
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

        #(5*CLK_PERIOD);

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
            #(CLK_PERIOD*burst_size*(length+20));
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

    task testFlow(int length, bit [31:0] flow_ctrl, bit [31:0] src_ip_mask);
        $write("\n######### Test of flows with packet length = %1d ", length);
        $write("(flow control: 0x%08h, SRC IP mask: 0x%08h) #########\n", flow_ctrl, src_ip_mask);
        scoreboard.setPktLen(length);
        scoreboard.setFlow(flow_ctrl, src_ip_mask);
        setFlow(flow_ctrl, src_ip_mask);
        enableTestEnvironment();
        enableGenerator(length, 0, 64);
        wait_burst_to_finish(length, 0, 0);
        disableGenerator();
        disableTestEnvironment();
        checkPktCounter(0, 0);
        scoreboard.display();
    endtask

    initial begin
        // Max burst size the burst mode is tested on
        const int max_bst_size = 10;
        // Flow control values: per packet, random, bursts of 4 and 16 packets
        const bit [31:0] flow_ctrls[5] = '{32'h01, 32'h03, 32'h21, 32'h23, 32'h41};
        // One word, a shifted start and several words per packet
        const int flow_lengths[3] = '{64, 129, 300};

        createEnvironment();
        resetDesign();

        if (USE_PACP_ARCH != 1'b1) begin
            $write("Test with different packet lengths and different burst sizes.\n");
            for (int bst_size = 1; bst_size < max_bst_size; bst_size=bst_size+3) begin
                for (int length = 64; length < 2*MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE; length=length+3) begin
                    test(length, 1, bst_size);
                end
            end
        end

        $write("Test without burst mode, the packets are sent continuously.\n");
        for (int length = 64; length < 4*MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE; length=length+3) begin
            test(length, 0, 64);
        end

        $write("Test of the SRC IP address flows.\n");
        foreach (flow_ctrls[i]) begin
            foreach (flow_lengths[j]) begin
                testFlow(flow_lengths[j], flow_ctrls[i], 32'h3FF);
            end
        end
        setFlow(32'h0, '1);
        scoreboard.setFlow(32'h0, '1);

        $write("Verification finished successfully!\n");
        $stop();
    end
endprogram
