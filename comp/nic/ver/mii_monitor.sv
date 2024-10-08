/*!
 * \file mii_ifc.sv
 * \brief Monitor of general MII transaction
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2016
 */
 /*
 * Copyright (C) 2016 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */



class MiiMonitor #(int WIDTH = 0, int LANE_WIDTH = 8) extends Monitor;

    // -- Private Class Attributes --
    localparam BYTES = WIDTH >> 3;
    localparam LANE_BYTES = LANE_WIDTH >> 3;

    localparam byte PREAMBLE_DATA[8] = {8'hFB, 8'h55, 8'h55, 8'h55, 8'h55, 8'h55, 8'h55, 8'hD5};
    localparam bit PREAMBLE_CTRL[8] = {1'b1, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0};

    local virtual iMiiTx#(WIDTH).tb mii;
    local int max_length;
    local int offset = 0;
    local logic [WIDTH-1 : 0] txd;
    local byte unsigned buffer[];


    // -- Public Class Methods --
    function new(string inst, virtual iMiiTx#(WIDTH).tb mii, int max_length = (1<<14));
        super.new(inst);
        WHOLE_BYTES_ONLY : assert(((WIDTH & 7) == 0) && ((LANE_WIDTH & 7) == 0));
        WHOLE_LANES_IN_WORD : assert((BYTES % LANE_BYTES) == 0);
        this.mii = mii;
        this.max_length = max_length;
        buffer = new[max_length + LANE_BYTES];
    endfunction


    // -- Private Class Methods --
    task moveLane();
        offset = offset + LANE_BYTES;
        if(offset >= BYTES) begin
            @(mii.cb);
            txd = mii.cb.TXD;
            offset = 0;
        end
    endtask

    task moveWord();
        @(mii.cb);
        txd = mii.cb.TXD;
        offset = 0;
    endtask

    virtual task run();
        Transaction transaction;
        MiiTransaction tr;
        int i, j;
        moveWord(); // initial sync
        while(enabled) begin
            tr = new;
            $cast(transaction, tr);
            foreach(cbs[i]) cbs[i].pre_rx(transaction, inst);
            while(1) begin  // Wait for valid start of frame
                busy = 0;
                while(1) begin // skip through idles
                    if(offset == 0 && (mii.cb.TXC == {BYTES{1'b1}}) && (txd == {BYTES{8'h07}}))
                        moveWord();
                    else if((mii.cb.TXC[offset +: LANE_BYTES] == {LANE_BYTES{1'b1}}) && (txd[8*offset +: 8*LANE_BYTES] == {LANE_BYTES{8'h07}}))
                        moveLane();
                    else
                        break;
                    if(!enabled) return;
                end
                busy = 1; // potential start of frame
                for(i = 0, j = offset; (i < 8) && (mii.cb.TXC[j] == PREAMBLE_CTRL[i]) && (txd[8*j +: 8] == PREAMBLE_DATA[i]); i++) begin
                    j++;
                    if(j >= offset + LANE_BYTES) begin
                        moveLane();
                        if(j >= BYTES)
                            j = 0;
                    end
                end
                if(i != 8) begin
                    $write("@%0t - %s: Error in MII protocol! Unexpected byte at position %0d.\n", $time, inst, j);
                    moveLane();
                end else
                    break;
            end
            i = 0;  // Receive transaction
            if(j != offset) begin
                for(j = j; j < offset+LANE_BYTES; j++, i++)
                    buffer[i] = txd[8*j +: 8];
                moveLane();
            end
            while(i < max_length) begin
                if(offset == 0 && mii.cb.TXC == 0) begin
                    buffer[i +: BYTES] = { << byte{txd} }; // store whole word
                    i = i + BYTES;
                    moveWord();
                end else begin // store one lane
                    buffer[i +: LANE_BYTES] = { << byte{txd[8*offset +: 8*LANE_BYTES]} };
                    if(mii.cb.TXC[offset +: LANE_BYTES] != 0)
                        break;
                    i = i + LANE_BYTES;
                    moveLane();
                end
                if(!enabled) return;
            end
            for(j = offset; mii.cb.TXC[j] == 0; j++, i++);
            if(buffer[i] != 'hFD)
                $write("@%0t - %s: Error in MII protocol! Wrong value of end of frame delimiter at position %0d.\n", $time, inst, j);
            for(j = j + 1; j < offset + LANE_BYTES; j++) // check idle bytes after frame
                if(mii.cb.TXC[j] != 1 || txd[8*j +: 8] != 8'h07) begin
                    $write("@%0t - %s: Error in MII protocol! Unexpected byte after frame end at position %0d.\n", $time, inst, j);
                    break;
                end
            moveLane();
            if(!enabled) return;
            tr.data = new[i-4](buffer); // Process frame data
            tr.crc = buffer[i-4 +: 4];
            foreach (cbs[i]) cbs[i].post_rx(transaction, inst);
            busy = 0;
        end
    endtask

endclass
