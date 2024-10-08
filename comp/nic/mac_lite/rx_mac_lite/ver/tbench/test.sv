// test.sv
// Copyright (C) 2019 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

import sv_common_pkg::*;
import sv_mi32_pkg::*;
import sv_mfb_pkg::*;
import sv_mvb_pkg::*;
import test_pkg::*;

program TEST (
    input  logic RX_CLK,
    input  logic TX_CLK,
    output logic ASYNC_RESET,

    iMi32.tb       MI,
    iMfbRx.tb      RX_MFB,
    iMfbTx.tb      TX_MFB,
    iMfbTx.monitor MFB_MONITOR,
    iMvbTx.tb      TX_MVB,
    iMvbTx.monitor MVB_MONITOR
);
    byte unsigned mac_array[MAC_COUNT_MAX][6] = '{default:0};

    MyTransaction myt_blueprint;
    Generator     generator;

    MfbDriver    #(RX_REGIONS,RX_REGION_SIZE,RX_BLOCK_SIZE,RX_ITEM_WIDTH,0,1,1) mfb_driver;
    MfbResponder #(TX_REGIONS,TX_REGION_SIZE,TX_BLOCK_SIZE,TX_ITEM_WIDTH) mfb_responder;
    MfbMonitor   #(TX_REGIONS,TX_REGION_SIZE,TX_BLOCK_SIZE,TX_ITEM_WIDTH) mfb_monitor;

    MvbResponder #(TX_REGIONS,METADATA_WIDTH) mvb_responder;
    MvbMonitor   #(TX_REGIONS,METADATA_WIDTH) mvb_monitor;

    Mi32Driver  mi32Driver;
    Mi32Monitor mi32Monitor;

    Scoreboard scoreboard;

    task createGeneratorEnvironment(int frame_size_max, int frame_size_min, int used_macs);
        // Generate random MAC addresses
        for (int i = 0; i < used_macs; i++)
            for (int j = 0; j < 6; j++)
                //mac_array[i][j] = i;
                mac_array[i][j] = i*3+j*13;

        generator = new("Generator", 0);
        myt_blueprint = new;
        myt_blueprint.dataSizeMax = frame_size_max;
        myt_blueprint.dataSizeMin = frame_size_min;
        myt_blueprint.mac_count   = used_macs;
        myt_blueprint.mac_array   = mac_array;
        generator.blueprint = myt_blueprint;
    endtask


    task createEnvironment();
        scoreboard = new(mac_array);

        mfb_driver = new("MFB Driver", generator.transMbx, RX_MFB);
        mfb_driver.setCallbacks(scoreboard.mfbDriverCbs);
        mfb_driver.wordDelayEnable_wt = 1;
        mfb_driver.wordDelayDisable_wt = 16;
        mfb_driver.wordDelayLow = 1;
        mfb_driver.wordDelayHigh = 6;
        mfb_driver.ifgEnable_wt = 2;
        mfb_driver.ifgDisable_wt = 10;
        mfb_driver.mode = 2;

        mfb_monitor = new("MFB Monitor", MFB_MONITOR);
        mfb_monitor.setCallbacks(scoreboard.mfbMonitorCbs);
        mfb_responder = new("MFB Responder", TX_MFB);

        mvb_monitor = new("MVB Monitor", MVB_MONITOR);
        mvb_monitor.setCallbacks(scoreboard.mvbMonitorCbs);
        mvb_responder = new("MVB Responder", TX_MVB);

        mi32Driver  = new("Mi32 Driver", null, MI);
        mi32Monitor = new("Mi32 Monitor", MI);

        mi32Driver.txDelayEn_wt      = 0;
        mi32Driver.txDelayDisable_wt = 1;
        mi32Driver.txDelayLow        = 0;
        mi32Driver.txDelayHigh       = 1;
    endtask


    task resetDesign();
        ASYNC_RESET = 1;
        #RESET_TIME ASYNC_RESET = 0;
    endtask


    task enableTestEnvironment();
        scoreboard.setEnabled();
        mfb_driver.setEnabled();
        mfb_monitor.setEnabled();
        mfb_responder.setEnabled();
        mvb_monitor.setEnabled();
        mvb_responder.setEnabled();
    endtask


    task disableTestEnvironment();
        int ready2stop;
        #(1000*TX_CLK_PERIOD);
        wait(!mfb_driver.busy);
        //$write("DisableTestEnvironment start, time: %t\n", $time);
        ready2stop = 0;
        do begin
            if (!mfb_monitor.busy && !mvb_monitor.busy) begin
                ready2stop++;
            end else begin
                ready2stop = 0;
            end;
            //$write("ready2stop %d, time: %t\n", ready2stop, $time);
            #(500*TX_CLK_PERIOD);
        end while (ready2stop < 100);
        #(5000*TX_CLK_PERIOD);
        //$write("DisableTestEnvironment ready, time: %t\n", $time);
        mfb_driver.setDisabled();
        mfb_monitor.setDisabled();
        mfb_responder.setDisabled();
        mvb_monitor.setDisabled();
        mvb_responder.setDisabled();
        scoreboard.setDisabled();
    endtask


    task initConfig();
        Mi32Transaction mi32_tr;

        bit [31:0] en_reg;

        // Set MI32 transaction
        mi32_tr = new();
        mi32_tr.rw = 1;
        mi32_tr.be = '1;

        // set MAC address to CAM memory
        for (int i = 0; i < MAC_COUNT; i++) begin
            // Send low 32 bits
            mi32_tr.address = 32'h80 + 8*i;
            { << byte {mi32_tr.data}} = mac_array[i][0:3];
            mi32Driver.sendTransaction(mi32_tr);

            // Send high 16 bits + valid bit
            mi32_tr.address = 32'h84 + 8*i;
            { << byte {mi32_tr.data[15:0]}} = mac_array[i][4:5];
            mi32_tr.data |= 32'h10000;    // Set valid bit
            mi32Driver.sendTransaction(mi32_tr);
        end

        // MAC address check mode
        mi32_tr.address = 32'h38;
        mi32_tr.data    = MAC_CHECK_MODE;
        mi32Driver.sendTransaction(mi32_tr);

        // Error mask register
        //TODO!!!

        // MinTU register (obsolete)
        mi32_tr.address = 32'h30;
        mi32_tr.data    = FRAME_LEN_MIN;
        mi32Driver.sendTransaction(mi32_tr);

        // MTU register
        mi32_tr.address = 32'h34;
        mi32_tr.data    = FRAME_LEN_MAX;
        mi32Driver.sendTransaction(mi32_tr);

        // Enable IBUF
        mi32_tr.address = 32'h20;
        mi32_tr.data    = 1;
        mi32Driver.sendTransaction(mi32_tr);

        // Read Enable IBUF due to verification sync
        mi32_tr.rw = 0;
        mi32_tr.address = 32'h20;
        mi32Monitor.executeTransaction(mi32_tr);
        en_reg = mi32_tr.data;

        #(10*MI_CLK_PERIOD);
    endtask


    task readCounters();
        Mi32Transaction mi32Transaction;
        automatic byte unsigned mac_array_read[MAC_COUNT_MAX][6] = '{default:0};

        bit [63:0] trfc;    // Total Received Frames Counter
        bit [63:0] cfc;     // Correct Frames Counter
        bit [63:0] dfc;     // Discarded Frames Counter
        bit [63:0] bofc;    // Counter of frames discarded due to buffer overflow
        bit [63:0] oroc;    // Octets Received OK Counter

        //Other RFC2819 counters
        bit [63:0] crc_err;             // Discarded frames due to bad CRC checksum
        bit [63:0] over_mtu;            // Discarded frames due to maximal MTU
        bit [63:0] below_min;           // Discarded frames due to minimal length
        bit [63:0] bcast_frames;        // Total Received broadcast frames
        bit [63:0] mcast_frames;        // Total Received multicast frames
        bit [63:0] fragment_frames;     // Total Received fragment frames
        bit [63:0] jabber_frames;       // Total Received jabber frames

        bit [63:0] frames_64;           //
        bit [63:0] frames_65_127;       //
        bit [63:0] frames_128_255;      //  Histogram
        bit [63:0] frames_256_511;      //  counters
        bit [63:0] frames_512_1023;     //
        bit [63:0] frames_1024_1518;    //
        bit [63:0] frames_over_1518;    //
        bit [63:0] frames_below_64;     //

        bit [63:0] trans_octets;        // Total received octets

        // Sample the current frame counters values
        mi32Transaction = new();
        mi32Transaction.address = 32'h2C;
        mi32Transaction.data    = 32'h1;
        mi32Transaction.rw      = 1;
        mi32Transaction.be      = '1;
        mi32Driver.sendTransaction(mi32Transaction);

        // wait few clock for sampling sync
        #(10*MI_CLK_PERIOD);

        mi32Transaction.rw      = 0;
        mi32Transaction.be      = '1;
        // Read Total Received Frames Counter
        // Low part
        mi32Transaction.address = 32'h00;
        mi32Monitor.executeTransaction(mi32Transaction);
        trfc[31:0]  = mi32Transaction.data;

        // High part
        mi32Transaction.address = 32'h10;
        mi32Monitor.executeTransaction(mi32Transaction);
        trfc[63:32] = mi32Transaction.data;

        // Read Correct Frames Counter
        // Low part
        mi32Transaction.address = 32'h04;
        mi32Monitor.executeTransaction(mi32Transaction);
        cfc[31:0]  = mi32Transaction.data;

        // High part
        mi32Transaction.address = 32'h14;
        mi32Monitor.executeTransaction(mi32Transaction);
        cfc[63:32] = mi32Transaction.data;

        // Read Discarded Frames Counter
        // Low part
        mi32Transaction.address = 32'h08;
        mi32Monitor.executeTransaction(mi32Transaction);
        dfc[31:0]  = mi32Transaction.data;

        // High part
        mi32Transaction.address = 32'h18;
        mi32Monitor.executeTransaction(mi32Transaction);
        dfc[63:32] = mi32Transaction.data;

        // Read Counter of frames discarded due to buffer overflow
        // Low part
        mi32Transaction.address = 32'h0C;
        mi32Monitor.executeTransaction(mi32Transaction);
        bofc[31:0]  = mi32Transaction.data;

        // High part
        mi32Transaction.address = 32'h1C;
        mi32Monitor.executeTransaction(mi32Transaction);
        bofc[63:32] = mi32Transaction.data;

        // Read Octets Received OK Counter
        // Low part
        mi32Transaction.address = 32'h3C;
        mi32Monitor.executeTransaction(mi32Transaction);
        oroc[31:0]  = mi32Transaction.data;

        // High part
        mi32Transaction.address = 32'h40;
        mi32Monitor.executeTransaction(mi32Transaction);
        oroc[63:32] = mi32Transaction.data;

        // Switch to the first statistics range from the IBUF
        if (USE_RFC2819_EXTENDED == 0) begin
            mi32Transaction.address = 32'h2C;
            mi32Transaction.data    = 32'h3;
            mi32Transaction.rw      = 1;
            mi32Transaction.be      = '1;
            mi32Driver.sendTransaction(mi32Transaction);

            mi32Transaction.rw      = 0;
            mi32Transaction.be      = '1;
        end

        // Read Counter of discarded frames due to bad CRC
        // Low part
        mi32Transaction.address = RFC2819_ADDRESSES[0][USE_RFC2819_EXTENDED];
        mi32Monitor.executeTransaction(mi32Transaction);
        crc_err[31:0]  = mi32Transaction.data;

        // High part
        mi32Transaction.address = RFC2819_ADDRESSES[14][USE_RFC2819_EXTENDED];
        mi32Monitor.executeTransaction(mi32Transaction);
        crc_err[63:32] = mi32Transaction.data;

        // Read Counter of discarded frames due to length over MTU
        // Low part
        mi32Transaction.address = RFC2819_ADDRESSES[1][USE_RFC2819_EXTENDED];
        mi32Monitor.executeTransaction(mi32Transaction);
        over_mtu[31:0]  = mi32Transaction.data;

        // High part
        mi32Transaction.address = RFC2819_ADDRESSES[15][USE_RFC2819_EXTENDED];
        mi32Monitor.executeTransaction(mi32Transaction);
        over_mtu[63:32] = mi32Transaction.data;

        // Read Counter of discarded frames due to length below min
        // Low part
        mi32Transaction.address = RFC2819_ADDRESSES[2][USE_RFC2819_EXTENDED];
        mi32Monitor.executeTransaction(mi32Transaction);
        below_min[31:0]  = mi32Transaction.data;

        // High part
        mi32Transaction.address = RFC2819_ADDRESSES[16][USE_RFC2819_EXTENDED];
        mi32Monitor.executeTransaction(mi32Transaction);
        below_min[63:32] = mi32Transaction.data;

        // Read Counter of broadcast frames
        // Low part
        mi32Transaction.address = RFC2819_ADDRESSES[3][USE_RFC2819_EXTENDED];
        mi32Monitor.executeTransaction(mi32Transaction);
        bcast_frames[31:0]  = mi32Transaction.data;

        // High part
        mi32Transaction.address = RFC2819_ADDRESSES[17][USE_RFC2819_EXTENDED];
        mi32Monitor.executeTransaction(mi32Transaction);
        bcast_frames[63:32] = mi32Transaction.data;

        // Read Counter of multicast frames
        // Low part
        mi32Transaction.address = RFC2819_ADDRESSES[4][USE_RFC2819_EXTENDED];
        mi32Monitor.executeTransaction(mi32Transaction);
        mcast_frames[31:0]  = mi32Transaction.data;

        // High part
        mi32Transaction.address = RFC2819_ADDRESSES[18][USE_RFC2819_EXTENDED];
        mi32Monitor.executeTransaction(mi32Transaction);
        mcast_frames[63:32] = mi32Transaction.data;

        // Read Counter of fragment frames
        // Low part
        mi32Transaction.address = RFC2819_ADDRESSES[5][USE_RFC2819_EXTENDED];
        mi32Monitor.executeTransaction(mi32Transaction);
        fragment_frames[31:0]  = mi32Transaction.data;

        // High part
        mi32Transaction.address = RFC2819_ADDRESSES[19][USE_RFC2819_EXTENDED];
        mi32Monitor.executeTransaction(mi32Transaction);
        fragment_frames[63:32] = mi32Transaction.data;

        // Read Counter of jabber frames
        // Low part
        mi32Transaction.address = RFC2819_ADDRESSES[6][USE_RFC2819_EXTENDED];
        mi32Monitor.executeTransaction(mi32Transaction);
        jabber_frames[31:0]  = mi32Transaction.data;

        // High part
        mi32Transaction.address = RFC2819_ADDRESSES[20][USE_RFC2819_EXTENDED];
        mi32Monitor.executeTransaction(mi32Transaction);
        jabber_frames[63:32] = mi32Transaction.data;

        // Read Counter of frames with transfered octets
        // Low part
        mi32Transaction.address = RFC2819_ADDRESSES[7][USE_RFC2819_EXTENDED];
        mi32Monitor.executeTransaction(mi32Transaction);
        trans_octets[31:0]  = mi32Transaction.data;

        // High part
        mi32Transaction.address = RFC2819_ADDRESSES[21][USE_RFC2819_EXTENDED];
        mi32Monitor.executeTransaction(mi32Transaction);
        trans_octets[63:32] = mi32Transaction.data;

        // Read Counter of frames with length = 64
        // Low part
        mi32Transaction.address = RFC2819_ADDRESSES[8][USE_RFC2819_EXTENDED];
        mi32Monitor.executeTransaction(mi32Transaction);
        frames_64[31:0]  = mi32Transaction.data;

        // High part
        mi32Transaction.address = RFC2819_ADDRESSES[22][USE_RFC2819_EXTENDED];
        mi32Monitor.executeTransaction(mi32Transaction);
        frames_64[63:32] = mi32Transaction.data;

        // Read Counter of frames with length >= 65 && 127 =< length
        // Low part
        mi32Transaction.address = RFC2819_ADDRESSES[9][USE_RFC2819_EXTENDED];
        mi32Monitor.executeTransaction(mi32Transaction);
        frames_65_127[31:0]  = mi32Transaction.data;

        // High part
        mi32Transaction.address = RFC2819_ADDRESSES[23][USE_RFC2819_EXTENDED];
        mi32Monitor.executeTransaction(mi32Transaction);
        frames_65_127[63:32] = mi32Transaction.data;

        // Read Counter of frames with length >= 128 && 255 =< length
        // Low part
        mi32Transaction.address = RFC2819_ADDRESSES[10][USE_RFC2819_EXTENDED];
        mi32Monitor.executeTransaction(mi32Transaction);
        frames_128_255[31:0]  = mi32Transaction.data;

        // High part
        mi32Transaction.address = RFC2819_ADDRESSES[24][USE_RFC2819_EXTENDED];
        mi32Monitor.executeTransaction(mi32Transaction);
        frames_128_255[63:32] = mi32Transaction.data;

        // Read Counter of frames with length >= 256 && 512 =< length
        // Low part
        mi32Transaction.address = RFC2819_ADDRESSES[11][USE_RFC2819_EXTENDED];
        mi32Monitor.executeTransaction(mi32Transaction);
        frames_256_511[31:0]  = mi32Transaction.data;

        // High part
        mi32Transaction.address = RFC2819_ADDRESSES[25][USE_RFC2819_EXTENDED];
        mi32Monitor.executeTransaction(mi32Transaction);
        frames_256_511[63:32] = mi32Transaction.data;

        // Read Counter of frames with length >= 512 && 1023 >= length
        // Low part
        mi32Transaction.address = RFC2819_ADDRESSES[12][USE_RFC2819_EXTENDED];
        mi32Monitor.executeTransaction(mi32Transaction);
        frames_512_1023[31:0]  = mi32Transaction.data;

        // High part
        mi32Transaction.address = RFC2819_ADDRESSES[26][USE_RFC2819_EXTENDED];
        mi32Monitor.executeTransaction(mi32Transaction);
        frames_512_1023[63:32] = mi32Transaction.data;

        // Read Counter of frames with length >= 1024 && 1518 >= length
        // Low part
        mi32Transaction.address = RFC2819_ADDRESSES[13][USE_RFC2819_EXTENDED];
        mi32Monitor.executeTransaction(mi32Transaction);
        frames_1024_1518[31:0]  = mi32Transaction.data;

        // High part
        mi32Transaction.address = RFC2819_ADDRESSES[27][USE_RFC2819_EXTENDED];
        mi32Monitor.executeTransaction(mi32Transaction);
        frames_1024_1518[63:32] = mi32Transaction.data;

        // Read Counter of frames with 1518 > length
        // Low part
        mi32Transaction.address = RFC2819_ADDRESSES[28][USE_RFC2819_EXTENDED];
        mi32Monitor.executeTransaction(mi32Transaction);
        frames_over_1518[31:0]  = mi32Transaction.data;

        // High part
        mi32Transaction.address = RFC2819_ADDRESSES[29][USE_RFC2819_EXTENDED];
        mi32Monitor.executeTransaction(mi32Transaction);
        frames_over_1518[63:32] = mi32Transaction.data;

        // Read Counter of frames below 64
        // Low part
        mi32Transaction.address = RFC2819_ADDRESSES[30][USE_RFC2819_EXTENDED];
        mi32Monitor.executeTransaction(mi32Transaction);
        frames_below_64[31:0]  = mi32Transaction.data;

        // High part
        mi32Transaction.address = RFC2819_ADDRESSES[31][USE_RFC2819_EXTENDED];
        mi32Monitor.executeTransaction(mi32Transaction);
        frames_below_64[63:32] = mi32Transaction.data;

        // Switch to the base range from the IBUF
        if (USE_RFC2819_EXTENDED == 0) begin
            mi32Transaction.address = 32'h2C;
            mi32Transaction.data    = 32'h3;
            mi32Transaction.rw      = 1;
            mi32Transaction.be      = '1;
            mi32Driver.sendTransaction(mi32Transaction);

            mi32Transaction.rw      = 0;
            mi32Transaction.be      = '1;
        end

        #(20*MI_CLK_PERIOD);

        // Display counters values
        $write("------------------------------------------------------------\n");
        $write("-- RX MAC LITE (DUT) Frame Counters\n");
        $write("------------------------------------------------------------\n");
        $write("Total Received Frames:               \t %10d\n",trfc);
        $write("Total Transmitted Frames:            \t %10d\n",cfc);
        $write("Total Discarded Frames:              \t %10d\n",dfc);
        $write("Discarded due to buffer overflow:    \t %10d\n",bofc);
        $write("Discarded due to length over MaxTU:  \t %10d\n",over_mtu);
        $write("Discarded due to length below MinTU: \t %10d\n",below_min);
        $write("Total Received Octets:               \t %10d\n",trans_octets);
        $write("Total Transmitted Octets:            \t %10d\n",oroc);
        $write("Total Received Frames with bad CRC:  \t %10d\n",crc_err);
        $write("Total Received Broadcast Frames:     \t %10d\n",bcast_frames);
        $write("Total Received Multicast Frames:     \t %10d\n",mcast_frames);
        $write("Total Received Fragment Frames:      \t %10d\n",fragment_frames);
        $write("Total Received Jabber Frames:        \t %10d\n",jabber_frames);
        $write("============================================================\n");
        $write("LENGTH HISTOGRAM OF TOTAL RECEIVED FRAMES:\n");
        $write("============================================================\n");
        $write("Undersize Frames  (<  64):           \t %10d\n",frames_below_64);
        $write("Frames with Length =  64:            \t %10d\n",frames_64);
        $write("Frames with Length >= 65 & <=127:    \t %10d\n",frames_65_127);
        $write("Frames with Length >= 128 & <=255:   \t %10d\n",frames_128_255);
        $write("Frames with Length >= 256 & <=511:   \t %10d\n",frames_256_511);
        $write("Frames with Length >= 512 & <=1023:  \t %10d\n",frames_512_1023);
        $write("Frames with Length >= 1024 & <=1518: \t %10d\n",frames_1024_1518);
        $write("Frames with Length >  1518:          \t %10d\n",frames_over_1518);
        $write("------------------------------------------------------------\n");

        // check MAC address from CAM memory
        $write("------------------------------------------------------------\n");
        $write("-- RX MAC LITE (DUT) CAM values\n");
        $write("------------------------------------------------------------\n");
        for (int i = 0; i < MAC_COUNT; i++) begin
            // Read low 32 bits
            mi32Transaction.address = 32'h80 + 8*i;
            mi32Monitor.executeTransaction(mi32Transaction);
            mac_array_read[i][0:3] = { << byte {mi32Transaction.data}};

            // Read high 16 bits + valid bit
            mi32Transaction.address = 32'h84 + 8*i;
            mi32Monitor.executeTransaction(mi32Transaction);
            mac_array_read[i][4:5] = { << byte {mi32Transaction.data[15:0]}};

            $write("MAC %10d:   \t %p\n",i,mac_array_read[i]);
            if (mac_array_read[i]!=mac_array[i]) begin
                $write("ERROR! Expected value for MAC %10d:   \t %p\n",i,mac_array[i]);
                $stop();
            end
        end

        if (cfc!=scoreboard.scoreTable.removed) begin
            $write("ERROR! The value of Transmitted Frames counter does not match the transaction table!\n");
            $write("Total Transmitted Frames:              \t %10d\n",cfc);
            $write("Removed frames from transaction table: \t %10d\n",scoreboard.scoreTable.removed);
            $stop();
        end

    endtask


    task test1();
        $write("\n\n############ TEST CASE 1 ############\n\n");
        //resetDesign();
        initConfig();
        enableTestEnvironment();
        generator.setEnabled(TRANSACTION_COUNT);
        wait(!generator.enabled);
        disableTestEnvironment();
        scoreboard.display();
        readCounters();
    endtask

    task test2();
        $write("\n\n############ TEST CASE 2 ############\n\n");
        //resetDesign();
        mfb_responder.wordDelayEnable_wt = 3;
        mfb_responder.wordDelayDisable_wt = 2;
        mfb_responder.wordDelayLow = 5;
        mfb_responder.wordDelayHigh = 20;
        mvb_responder.wordDelayEnable_wt = 2;
        mvb_responder.wordDelayDisable_wt = 1;
        mvb_responder.wordDelayLow = 5;
        mvb_responder.wordDelayHigh = 20;
        initConfig();
        enableTestEnvironment();
        generator.setEnabled(TRANSACTION_COUNT);
        wait(!generator.enabled);
        disableTestEnvironment();
        scoreboard.display();
        readCounters();
    endtask

    initial begin
        resetDesign();
        createGeneratorEnvironment(FRAME_SIZE_MAX, FRAME_SIZE_MIN, MAC_COUNT);
        createEnvironment();
        test1();
        test2();
        $write("Verification finished successfully!\n");
        $stop();
    end

endprogram
