/*!
 * \file mfb_ifc.sv
 * \brief Multi-Frame Bus interface
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2016
 */
 /*
 * Copyright (C) 2016 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

//import math_pkg::*;



// /////////////////////////////////////////////////////////////////////////////
// Multi-Frame Bus RX (verification to DUT) interface
interface iMfbRx #(REGIONS = 4, REGION_SIZE = 8, BLOCK_SIZE = 8, ITEM_WIDTH = 8, META_WIDTH = 1) (input logic CLK, RESET);
    initial VALID_PARAMETERS : assert(REGIONS > 0 && REGION_SIZE > 0 && BLOCK_SIZE > 0 && ITEM_WIDTH > 0);

    localparam WORD_WIDTH = REGIONS * REGION_SIZE * BLOCK_SIZE * ITEM_WIDTH;
    localparam META_WORD_WIDTH = REGIONS * META_WIDTH;
    localparam SOF_POS_WIDTH = math_pkg::max(1,math_pkg::log2(REGION_SIZE));
    localparam EOF_POS_WIDTH = math_pkg::max(1,math_pkg::log2(REGION_SIZE * BLOCK_SIZE));


    wire logic [WORD_WIDTH-1 : 0] DATA;
    wire logic [META_WORD_WIDTH-1 : 0] META;
    wire logic [REGIONS * SOF_POS_WIDTH-1 : 0] SOF_POS;
    wire logic [REGIONS * EOF_POS_WIDTH-1 : 0] EOF_POS;
    wire logic [REGIONS-1 : 0] SOF;
    wire logic [REGIONS-1 : 0] EOF;
    wire logic SRC_RDY;
    wire logic DST_RDY;

    clocking cb @(posedge CLK);
        default input #1step output #500ps;
        output DATA, META, SOF_POS, EOF_POS, SOF, EOF, SRC_RDY;
        input DST_RDY;
    endclocking;

    clocking monitor_cb @(posedge CLK);
        default input #1step output #500ps;
        input DATA, META, SOF_POS, EOF_POS, SOF, EOF, SRC_RDY, DST_RDY;
    endclocking: monitor_cb;


    modport dut (input DATA, META, SOF_POS, EOF_POS, SOF, EOF, SRC_RDY, output DST_RDY);

    modport tb (clocking cb);

    modport monitor (clocking monitor_cb);



    ///////////////////////
    // Local variables for assumptions
    logic pkt_vld;
    logic sof_correct[REGIONS];
    logic eof_correct[REGIONS];

    always_ff @(posedge CLK) begin
        if (RESET) begin
            pkt_vld = 0;
            sof_correct = '{REGIONS {1'b1}};
            eof_correct = '{REGIONS {1'b1}};
        end else begin
            if (SRC_RDY === 1'b1 && DST_RDY === 1'b1) begin
                for (int unsigned it = 0; it < REGIONS; it++) begin
                    //automatic int unsigned sof_pos = 0;
                    automatic int unsigned sof_pos = (REGION_SIZE > 1)              ? SOF_POS[(it+1)*SOF_POS_WIDTH-1 -: SOF_POS_WIDTH]*BLOCK_SIZE : 0;
                    automatic int unsigned eof_pos = (REGION_SIZE * BLOCK_SIZE > 1) ? EOF_POS[(it+1)*EOF_POS_WIDTH-1 -: EOF_POS_WIDTH]            : 0;

                    if (SOF[it] && (!EOF[it] || sof_pos <= eof_pos)) begin
                        sof_correct[it] <= (pkt_vld === 0);
                        pkt_vld = 1;
                    end

                    if (EOF[it]) begin
                        eof_correct[it] <= (pkt_vld === 1);
                        pkt_vld = 0;
                    end

                    if (SOF[it] && EOF[it] && sof_pos > eof_pos) begin
                        sof_correct[it] <= (pkt_vld === 0);
                        pkt_vld = 1;
                    end
                end
            end
        end
    end


    property signal_correct;
        (sof_correct === '{REGIONS {1'b1}}) && (eof_correct === '{REGIONS {1'b1}});
    endproperty

    property src_correct;
        (SRC_RDY === 1'b1) |-> (pkt_vld || SOF !== 0);
    endproperty

    assume property ( @(posedge CLK) disable iff (RESET) signal_correct) else $stop();

    assume property ( @(posedge CLK) disable iff (RESET) src_correct) else $stop();

    assert property ( @(posedge CLK) disable iff (RESET) !$isunknown(DST_RDY)) else $stop();
    assume property ( @(posedge CLK) disable iff (RESET) !$isunknown(SRC_RDY)) else $stop();

endinterface



// /////////////////////////////////////////////////////////////////////////////
// Multi-Frame Bus TX (DUT to verification) interface
interface iMfbTx #(REGIONS = 4, REGION_SIZE = 8, BLOCK_SIZE = 8, ITEM_WIDTH = 8, META_WIDTH = 1) (input logic CLK, RESET);
    initial VALID_PARAMETERS : assert(REGIONS > 0 && REGION_SIZE > 0 && BLOCK_SIZE > 0 && ITEM_WIDTH > 0);

    localparam WORD_WIDTH = REGIONS * REGION_SIZE * BLOCK_SIZE * ITEM_WIDTH;
    localparam META_WORD_WIDTH = REGIONS * META_WIDTH;
    localparam SOF_POS_WIDTH = math_pkg::max(1,math_pkg::log2(REGION_SIZE));
    localparam EOF_POS_WIDTH = math_pkg::max(1,math_pkg::log2(REGION_SIZE * BLOCK_SIZE));


    wire logic [WORD_WIDTH-1 : 0] DATA;
    wire logic [META_WORD_WIDTH-1 : 0] META;
    wire logic [REGIONS * SOF_POS_WIDTH-1 : 0] SOF_POS;
    wire logic [REGIONS * EOF_POS_WIDTH-1 : 0] EOF_POS;
    wire logic [REGIONS-1 : 0] SOF;
    wire logic [REGIONS-1 : 0] EOF;
    wire logic SRC_RDY;
    wire logic DST_RDY;


    clocking cb @(posedge CLK);
        default input #1step output #500ps;
        input DATA, META, SOF_POS, EOF_POS, SOF, EOF, SRC_RDY;
        output DST_RDY;
    endclocking;

    clocking monitor_cb @(posedge CLK);
        default input #1step output #500ps;
        input DATA, META, SOF_POS, EOF_POS, SOF, EOF, SRC_RDY, DST_RDY;
    endclocking: monitor_cb;


    modport dut (output DATA, META, SOF_POS, EOF_POS, SOF, EOF, SRC_RDY, input DST_RDY);

    modport tb (clocking cb);

    modport monitor (clocking monitor_cb);


    ///////////////////////
    // Local variables for assertions
    logic pkt_vld;
    logic sof_correct[REGIONS];
    logic eof_correct[REGIONS];

    always_ff @(posedge CLK) begin
        if (RESET) begin
            pkt_vld = 0;
            sof_correct = '{REGIONS {1'b1}};
            eof_correct = '{REGIONS {1'b1}};
        end else begin
            if (SRC_RDY === 1'b1 && DST_RDY === 1'b1) begin
                for (int unsigned it = 0; it < REGIONS; it++) begin
                    //automatic int unsigned sof_pos = 0;
                    automatic int unsigned sof_pos = (REGION_SIZE > 1)              ? SOF_POS[(it+1)*SOF_POS_WIDTH-1 -: SOF_POS_WIDTH]*BLOCK_SIZE : 0;
                    automatic int unsigned eof_pos = (REGION_SIZE * BLOCK_SIZE > 1) ? EOF_POS[(it+1)*EOF_POS_WIDTH-1 -: EOF_POS_WIDTH]            : 0;

                    if (SOF[it] && (!EOF[it] || sof_pos <= eof_pos)) begin
                        sof_correct[it] <= (pkt_vld === 0);
                        pkt_vld = 1;
                    end

                    if (EOF[it]) begin
                        eof_correct[it] <= (pkt_vld === 1);
                        pkt_vld = 0;
                    end

                    if (SOF[it] && EOF[it] && sof_pos > eof_pos) begin
                        sof_correct[it] <= (pkt_vld === 0);
                        pkt_vld = 1;
                    end
                end
            end
        end
    end


    property signal_correct;
        (sof_correct === '{REGIONS {1'b1}}) && (eof_correct === '{REGIONS {1'b1}});
    endproperty

    property src_correct;
        (SRC_RDY === 1'b1) |-> (pkt_vld || SOF !== 0);
    endproperty

    assert property ( @(posedge CLK) disable iff (RESET) signal_correct) else $stop();

    assert property ( @(posedge CLK) disable iff (RESET) src_correct) else $stop();

    assert property ( @(posedge CLK) disable iff (RESET) !$isunknown(SRC_RDY)) else $stop();
    assume property ( @(posedge CLK) disable iff (RESET) !$isunknown(DST_RDY)) else $stop();
endinterface

