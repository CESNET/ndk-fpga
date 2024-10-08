// scoreboard.sv
// Copyright (C) 2020 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

import sv_common_pkg::*;
import sv_mfb_pkg::*;

class ScoreboardMonitorCbs extends MonitorCbs;
    longint cnt;
    int expPktLen;

    function new ();
        cnt = 0;
        expPktLen = 0;
    endfunction

    virtual task post_rx(Transaction transaction, string inst);
        MfbTransaction #(MFB_ITEM_WIDTH) mfbTrans;
        int pktLen;
        int error;
        error = 0;
        cnt = cnt + 1;
        $cast(mfbTrans, transaction);
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

    function longint getPktCounter();
        return this.monitorCbs.cnt;
    endfunction;

endclass
