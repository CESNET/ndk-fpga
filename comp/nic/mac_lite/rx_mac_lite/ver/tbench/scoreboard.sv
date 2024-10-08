// scoreboard.sv
// Copyright (C) 2019 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

import sv_common_pkg::*;
import sv_mvb_pkg::*;
import sv_mfb_pkg::*;
import sv_stats_pkg::*;
import test_pkg::*;

class Model;
    bit                      enabled;
    // Transaction table
    TransactionTable #(0)    sc_table;
    // RX mailbox
    mailbox                  rxMbx;
    // RFC2819 Update mailbox
    mailbox #(RFC2819Update) statMbx;
    // Array of allowed MAC address
    byte unsigned            mac_array[MAC_COUNT_MAX][6];

    function new (TransactionTable #(0) st, mailbox Mbx, mailbox #(RFC2819Update) updateMbx, byte unsigned mac_arr[MAC_COUNT_MAX][6]);
        this.sc_table  = st;
        this.rxMbx     = Mbx;
        this.statMbx   = updateMbx;
        this.mac_array = mac_arr;
    endfunction

    task setEnabled();
        enabled = 1; // Model Enabling
        fork
            run(); // Creating model subprocess
        join_none; // Don't wait for ending
    endtask

    task setDisabled();
        enabled = 0; // Disable model
    endtask

    task checkMAC(MyTransaction #(RX_ITEM_WIDTH) frame);
        bit is_mac_bcast = 1;
        bit is_mac_mcast = 0;
        bit is_allowed_mac = 0;

        for (int i=0; i < 6; i++) begin
            if (frame.data[i] != 8'hFF) begin
                is_mac_bcast = 0;
                break;
            end
        end

        if (frame.data[0][0] == 1)
            is_mac_mcast = 1;

        // Check available MACs
        for (int i = 0; i < MAC_COUNT; i++) begin
            int matchingBytes;
            matchingBytes = 0;

            for (int j = 0; j < 6; j++) begin
                // frame.data is in network format (big endian) => MSB byte first!
                if (frame.data[j] == mac_array[i][5-j])
                matchingBytes++;
                else break;
            end

            if (matchingBytes == 6) begin
                is_allowed_mac = 1;
                frame.mac_index = i;
                break;
            end
        end

        case (MAC_CHECK_MODE)
            0 : frame.mac_error = 0;
            1 : frame.mac_error = !is_allowed_mac;
            2 : frame.mac_error = (!is_allowed_mac && !is_mac_bcast);
            3 : frame.mac_error = (!is_allowed_mac && !is_mac_bcast && !is_mac_mcast);
            default : $write("Error in MAC_CHECK_MODE SEL \n");
        endcase

        frame.mac_hit   = is_allowed_mac;
        frame.mac_mcast = is_mac_mcast;
        frame.mac_bcast = is_mac_bcast;
    endtask

    task run();
        Transaction   mbx_tr;
        MyTransaction #(RX_ITEM_WIDTH) frame;
        RFC2819Update stat;
        int frame_len_max_fix;
        int frame_len_min_fix;

        if (CRC_REMOVE_EN || (!CRC_IS_RECEIVED)) begin
            frame_len_max_fix = FRAME_LEN_MAX - 4;
            frame_len_min_fix = FRAME_LEN_MIN - 4;
        end else begin
            frame_len_max_fix = FRAME_LEN_MAX;
            frame_len_min_fix = FRAME_LEN_MIN;
        end

        while (enabled) begin // Repeat while enabled
            //$write("wait for My transaction in DUT model, time: %t\n", $time);
            rxMbx.get(mbx_tr);
            $cast(frame, mbx_tr);

            if (CRC_REMOVE_EN) begin
                // cut CRC from data
                //$write("Frame before cut CRC:\n");
                //frame.display();
                if (frame.data.size >= 4) begin
                    frame.data = new[frame.data.size-4](frame.data);
                end
            end
            //$write("Frame after cut CRC:\n");
            //frame.display();

            if (MAC_CHECK_EN) begin
                checkMAC(frame);
            end else begin
                frame.mac_error = 0;
                frame.mac_mcast = 0;
                frame.mac_bcast = 0;
                frame.mac_type  = 0;
                frame.mac_index = 0;
            end

            stat = new();
            stat.newPacket = 1;

            if (CRC_CHECK_EN) begin
                stat.crcErr = frame.crc_error;
            end else begin
                frame.crc_error = 0;
                stat.crcErr = 0;
            end

            // Frame length with CRC for stat model
            if (CRC_IS_RECEIVED && CRC_REMOVE_EN) begin
                stat.packetLength = frame.data.size - 4;
            end else begin
                stat.packetLength = frame.data.size;
            end

            if (frame.data.size > frame_len_max_fix) begin
                frame.maxtu_error = 1;
                stat.MTUErr = 1;
                stat.discardedFrame = 1;
            end

            if (frame.data.size < frame_len_min_fix) begin
                frame.mintu_error = 1;
                stat.mintuErr = 1;
                stat.discardedFrame = 1;
            end

            frame.error = frame.adapter_error || frame.mac_error || frame.mintu_error || frame.maxtu_error || frame.crc_error;

            //$write("Frame in model:\n");
            //frame.display();

            if (!frame.error) begin
                sc_table.add(frame);
            end

            statMbx.put(stat);

            stat = new();
            stat.multicastFrame = frame.mac_mcast;
            stat.broadcastFrame = frame.mac_bcast;
            statMbx.put(stat);
        end
    endtask

endclass


class Checker;
    bit                      enabled;
    // Transaction table
    TransactionTable #(0)    sc_table;
    // MFB mailbox
    tTransMbx                  mfbMbx;
    // MVB mailbox
    tTransMbx                  mvbMbx;

    function new (TransactionTable #(0) st, tTransMbx fMbx, tTransMbx vMbx);
        this.sc_table  = st;
        this.mfbMbx    = fMbx;
        this.mvbMbx    = vMbx;
    endfunction

    task setEnabled();
        enabled = 1; // Model Enabling
        fork
            run(); // Creating model subprocess
        join_none; // Don't wait for ending
    endtask

    task setDisabled();
        enabled = 0; // Disable model
    endtask

    task run();
        bit status = 0;
        int lenght = 0;
        Transaction                      mbx_mfb_tr;
        MfbTransaction #(RX_ITEM_WIDTH)     mfb_tr;
        Transaction                      mbx_mvb_tr;
        MvbTransaction #(METADATA_WIDTH) mvb_tr;
        MyTransaction #(RX_ITEM_WIDTH)      tx_tr;

        while (enabled) begin // Repeat while enabled
            status = 0;

            wait ((mfbMbx.num() != 0) || (!enabled));

            if (!enabled) begin
                continue;
            end

            mfbMbx.get(mbx_mfb_tr);
            $cast(mfb_tr, mbx_mfb_tr);

            //$write("MFB!\n");
            //mfb_tr.display();

            mvbMbx.get(mbx_mvb_tr);
            $cast(mvb_tr, mbx_mvb_tr);
            lenght = mvb_tr.data[15:0];

            tx_tr = new();
            tx_tr.data = new[lenght](mfb_tr.data);

            tx_tr.error         = mvb_tr.data[24];
            tx_tr.adapter_error = mvb_tr.data[25];
            tx_tr.mintu_error   = mvb_tr.data[26];
            tx_tr.maxtu_error   = mvb_tr.data[27];
            tx_tr.crc_error     = mvb_tr.data[28];
            tx_tr.mac_error     = mvb_tr.data[29];
            tx_tr.mac_bcast     = mvb_tr.data[30];
            tx_tr.mac_mcast     = mvb_tr.data[31];
            tx_tr.mac_hit       = mvb_tr.data[32];
            tx_tr.mac_index     = mvb_tr.data[36:33];

            // TODO - ONLY FOR META ALIGNED TO SOF
            //if (mfb_tr.sof != mvb_tr.stream) begin
            //    $write("SOF and metadata positions do not match!\n");
            //    mfb_tr.display();
            //    mvb_tr.display();
            //    tx_tr.display();
            //    $stop;
            //end

            sc_table.remove(tx_tr, status);
            if (status==0)begin
                $write("Unknown transaction in DUT checker\n");
                $timeformat(-9, 3, " ns", 8);
                $write("Time: %t\n", $time);
                tx_tr.display();
                $write("MFB mailbox status: %d\n", mfbMbx.num());
                $write("MVB mailbox status: %d\n", mvbMbx.num());
                sc_table.display();
                $stop;
            end;
            //$write("FRAME IS OK!\n");
            //tx_tr.display();
        end
    endtask
endclass


class ScoreboardMfbDriverCbs extends DriverCbs;
    mailbox RxMbx;
    int cnt = 0;

    function new (mailbox Mbx);
        this.RxMbx = Mbx;
    endfunction

    virtual task pre_tx(ref Transaction transaction, string inst);
        MfbTransaction #(RX_ITEM_WIDTH) mfb_tr;
        MyTransaction  #(RX_ITEM_WIDTH) my_tr;
        transaction.post_randomize(); // compute CRC
        //$write("New transaction received by driver, time: %t\n", $time);
        //transaction.display();
        RxMbx.put(transaction);
        cnt = cnt + 1;
        if ((cnt % 1000) == 0) begin
            $write("%0d transactions sent to DUT.\n", cnt);
        end;
        // MY to MFB
        $cast(my_tr, transaction);
        mfb_tr = new();
        mfb_tr.data = new[my_tr.data.size](my_tr.data);
        mfb_tr.meta[0] = my_tr.adapter_error;
        $cast(transaction, mfb_tr);
    endtask

    virtual task post_tx(Transaction transaction, string inst);
        //$write("New transaction posted by driver, time: %t\n", $time);
        //transaction.display();
    endtask
endclass


class ScoreboardMfbMonitorCbs extends MonitorCbs;
    tTransMbx mfbMbx;

    function new (tTransMbx Mbx);
        this.mfbMbx = Mbx;
    endfunction

    virtual task post_rx(Transaction transaction, string inst);
        //$write("New MFB transaction received, time: %t\n", $time);
        //transaction.display();
        mfbMbx.put(transaction);
    endtask
endclass


class ScoreboardMvbMonitorCbs extends MonitorCbs;
    tTransMbx mvbMbx;

    function new (tTransMbx Mbx);
        this.mvbMbx = Mbx;
    endfunction

    virtual task post_rx(Transaction transaction, string inst);
        //$write("New MVB transaction received, time: %t\n", $time);
        //transaction.display();
        mvbMbx.put(transaction);
    endtask
endclass


class Scoreboard;
    Model                     dutModel;
    Checker                   dutCheck;
    TransactionTable #(0)     scoreTable;
    // RFC2819 Statistics communication channel
    mailbox #(RFC2819Update)  updateMbx;
    // RFC2819 statistics module
    RFC2819Statistics         statModule;
    tTransMbx                   mvbMbx;
    tTransMbx                   mfbMbx;
    mailbox                   rxMbx;
    ScoreboardMfbDriverCbs    mfbDriverCbs;
    ScoreboardMfbMonitorCbs   mfbMonitorCbs;
    ScoreboardMvbMonitorCbs   mvbMonitorCbs;

    function new (byte unsigned mac_arr[MAC_COUNT_MAX][6]);
        scoreTable    = new;
        //RFC2819 statistics
        updateMbx     = new();
        statModule    = new(updateMbx);
        mvbMbx        = new();
        mfbMbx        = new();
        rxMbx         = new();
        mfbDriverCbs  = new(rxMbx);
        mfbMonitorCbs = new(mfbMbx);
        mvbMonitorCbs = new(mvbMbx);
        dutModel      = new(scoreTable,rxMbx,updateMbx,mac_arr);
        dutCheck      = new(scoreTable,mfbMbx,mvbMbx);
    endfunction

    task setEnabled();
        dutModel.setEnabled(); // Enable model
        dutCheck.setEnabled(); // Enable checker
        statModule.setEnabled(); //Enable RFC2819 module
    endtask

    task setDisabled();
        dutModel.setDisabled(); // Disable model
        dutCheck.setDisabled(); // Disable checker
        statModule.setDisabled(); //Disable RFC2819 module
    endtask

    task display();
        scoreTable.display(0,"RX MAC LITE ScoreTable");
        $write("MFB mailbox status: %d\n", mfbMbx.num());
        $write("MVB mailbox status: %d\n", mvbMbx.num());
        statModule.display("RFC2819 Counters");
    endtask
endclass
