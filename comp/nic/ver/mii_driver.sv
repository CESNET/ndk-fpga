/*!
 * \file mii_driver.sv
 * \brief Driver for general MII interface
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



class MiiDriver #(int WIDTH = 0, int LANE_WIDTH = 8) extends Driver;

    // -- Private Class Attributes --
    localparam BYTES = WIDTH >> 3;
    localparam LANE_BYTES = LANE_WIDTH >> 3;

    localparam byte unsigned PREAMBLE_DATA[8] = {8'hFB, 8'h55, 8'h55, 8'h55, 8'h55, 8'h55, 8'h55, 8'hD5};
    localparam byte unsigned EMPTY_DATA[LANE_BYTES] = '{LANE_BYTES{8'h07}};

    protected virtual iMiiRx#(WIDTH).tb mii;
    protected int offset = 0;
    protected byte unsigned rxd[BYTES];


    // -- Public Class Methods --
    function new(string inst, tTransMbx transMbx, virtual iMiiRx#(WIDTH).tb mii);
        super.new(inst, transMbx);
        WHOLE_BYTES_ONLY : assert(((WIDTH & 7) == 0) && ((LANE_WIDTH & 7) == 0));
        WHOLE_LANES_IN_WORD : assert((BYTES % LANE_BYTES) == 0);
        this.mii = mii;
        this.mii.cb.RXC <= {BYTES{1'b1}};
        this.rxd = '{BYTES{8'h07}};
    endfunction


    // -- Private Class Methods --
    task moveLane();
        offset = offset + LANE_BYTES;
        if(offset >= BYTES) begin
            moveWord();
        end
    endtask

    task moveWord();
        this.mii.cb.RXD <= { << byte{rxd} };
        @(mii.cb);
        this.mii.cb.RXC <= {BYTES{1'b1}};
        rxd = '{BYTES{8'h07}};
        offset = 0;
    endtask

    virtual task run();
        Transaction transaction;
        MiiTransaction tr;
        byte unsigned data[];
        int i, j, n, idleCount, idle;
        idleCount = 4;
        @(mii.cb); // initial sync
        while(enabled) begin
            while(transMbx.try_get(transaction) == 0) begin
                moveWord();
                if (!enabled) return;
            end
            busy = 1; // delay before transaction
            assert(randomize());
            if(enDelay)
                repeat(delay)
                    moveLane();
            foreach(cbs[i]) cbs[i].pre_tx(transaction, inst);
            $cast(tr, transaction); // send transaction
            if(tr.miiError) begin // Inserting possible MII error into transaction data
                tr.data[tr.miiErrorPos] = 8'hFE;
                tr.post_randomize(); // crc recompute
            end
            data = {PREAMBLE_DATA, tr.data, tr.crc, 8'hFD, EMPTY_DATA};
            n = data.size - LANE_BYTES; i = 0;
            while(i < n) // transaction written onto bus
                if(offset == 0 && (data.size-i) > BYTES) begin
                    rxd = data[i +: BYTES];
                    mii.cb.RXC <= {BYTES{1'b0}};
                    if(i == 0)
                        mii.cb.RXC[0] <= 1;
                    if(tr.miiError && (tr.miiErrorPos+8) >= i && (tr.miiErrorPos+8) < (i+BYTES))
                        mii.cb.RXC[(tr.miiErrorPos+8) - i] <= 1;
                    for(j = data.size - 1 - LANE_BYTES - i; j < BYTES; j++)
                        mii.cb.RXC[j] <= 1;
                    moveWord();
                    i = i + BYTES;
                end else begin
                    rxd[offset +: LANE_BYTES] = data[i +: LANE_BYTES];
                    mii.cb.RXC[offset +: LANE_BYTES] <= {LANE_BYTES{1'b0}};
                    if(i == 0)
                        mii.cb.RXC[offset] <= 1;
                    if(tr.miiError && (tr.miiErrorPos+8) >= i && (tr.miiErrorPos+8) < (i+LANE_BYTES))
                        mii.cb.RXC[offset + (tr.miiErrorPos+8) - i] <= 1;
                    for(j = data.size - 1 - LANE_BYTES - i; j < LANE_BYTES; j++)
                        mii.cb.RXC[offset + j] <= 1;
                    moveLane();
                    i = i + LANE_BYTES;
                end
            foreach(cbs[i]) cbs[i].post_tx(transaction, inst);
            idle = i - (tr.data.size + 12);
            while(idle < 4) begin
                moveLane();
                idle = idle + LANE_BYTES;
            end
            idleCount = idleCount + idle;
            while(idleCount < 12) begin
                moveLane();
                idleCount = idleCount + LANE_BYTES;
            end
            idleCount = idleCount - 12;
            busy = 0;
        end
    endtask

endclass
