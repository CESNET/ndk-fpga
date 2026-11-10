// scoreboard.sv
// Copyright (C) 2020 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

import sv_common_pkg::*;
import sv_mfb_pkg::*;

// Model of the flow_mix function in MFB_GENERATOR
function automatic bit [31:0] flow_mix(bit [31:0] x);
    bit [31:0] v;
    v = x ^ (x << 12);
    v = v ^ (v >> 4);
    v = (~v) + (v << 7);
    v = v ^ (v >> 6);
    v = v ^ (v << 8);
    v = v + (v << 5);
    v = v ^ (v >> 16);
    return v;
endfunction

class ScoreboardMonitorCbs extends MonitorCbs;
    longint cnt;
    int expPktLen;
    // Value of the flow control register (0x2C) and of the SRC IP mask (0x28)
    bit [31:0] flowCtrl;
    bit [31:0] srcIpMask;

    function new ();
        cnt = 0;
        expPktLen = 0;
        flowCtrl = 0;
        srcIpMask = '1;
    endfunction

    virtual task post_rx(Transaction transaction, string inst);
        MfbTransaction #(MFB_ITEM_WIDTH) mfbTrans;
        int pktLen;
        int error;
        bit [31:0] idx;
        bit [31:0] expSrcIp;
        bit [31:0] srcIp;
        error = 0;
        $cast(mfbTrans, transaction);

        // With per_pkt = 1 the SRC IP address is derived from the packet index.
        // The test starts the index from 0 before each run, the same as cnt.
        if (flowCtrl[0]) begin
            idx = cnt >> flowCtrl[7:4];
            expSrcIp = (flowCtrl[1] ? flow_mix(idx) : idx) & srcIpMask;
            srcIp = {mfbTrans.data[29], mfbTrans.data[28], mfbTrans.data[27], mfbTrans.data[26]};
            if (srcIp != expSrcIp) begin
                $write("SRC IP address of packet %0d is 0x%08h, expected 0x%08h\n", cnt, srcIp, expSrcIp);
                error = 1;
            end
        end
        cnt = cnt + 1;
        //transaction.display();

        if (mfbTrans.data.size() != expPktLen)
            error = 1;
        // verify SRC and DST MAC address
        for(int j=0; j < 6; j++) begin
            if(8'hFF != mfbTrans.data[j]) begin
                $write("Byte %1d does not match\n", j);
                error = 1;
                break;
            end
        end
        if(8'h00 != mfbTrans.data[6]) begin
            $write("Byte 6 does not match\n");
            error = 1;
        end
        if(8'h11 != mfbTrans.data[7]) begin
            $write("Byte 7 does not match\n");
            error = 1;
        end
        if(8'h17 != mfbTrans.data[8]) begin
            $write("Byte 8 does not match\n");
            error = 1;
        end
        if(8'h60 != mfbTrans.data[9]) begin
            $write("Byte 9 does not match\n");
            error = 1;
        end
        for(int j=10; j < 12; j++) begin
            if(8'h0 != mfbTrans.data[j]) begin
                $write("Byte %1d does not match\n", j);
                error = 1;
                break;
            end
        end

        if (error == 1) begin
            $write("Transaction with bad length or bytes! Expected length is %0d.\n", expPktLen);
            $timeformat(-9, 3, " ns", 8);
            $write("Time: %t\n", $time);
            transaction.display();
            $stop;
        end;
    endtask
endclass

class Scoreboard;
    ScoreboardMonitorCbs monitorCbs;

    function new ();
        monitorCbs = new();
    endfunction

    task display();
        $write("%0d transactions received by monitor.\n", this.monitorCbs.cnt);
    endtask

    task setPktLen(int length);
        this.monitorCbs.expPktLen = length;
        this.monitorCbs.cnt = 0;
    endtask

    task setFlow(bit [31:0] flow_ctrl, bit [31:0] src_ip_mask);
        this.monitorCbs.flowCtrl = flow_ctrl;
        this.monitorCbs.srcIpMask = src_ip_mask;
    endtask

    function longint getPktCounter();
        return this.monitorCbs.cnt;
    endfunction;

endclass
