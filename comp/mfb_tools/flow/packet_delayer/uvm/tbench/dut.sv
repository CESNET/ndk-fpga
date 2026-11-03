// dut.sv: Design under test
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
// SPDX-License-Identifier: BSD-3-Clause

import test::*;

module dut (
    input logic             CLK,
    input logic             RST,
    input logic             TIME_RESET,
    input logic[64-1 : 0]   CURRENT_TIME,
    output logic            PAUSE_REQUEST,
    mfb_if.dut_rx           mfb_rx,
    mfb_if.dut_tx           mfb_tx
    );

    parameter int EXTENDED_META_WIDTH = META_WIDTH+TS_WIDTH;

    logic [REGIONS*META_WIDTH-1 : 0] meta;
    logic [REGIONS*TS_WIDTH-1 : 0]      timestamp;

    generate
        for (genvar r = 0; r < REGIONS; r++) begin : gen_r
            // Extended meta per region: [E-1:TS_WIDTH]=META, [TS_WIDTH-1:0]=TIMESTAMP
            if (META_WIDTH > 0) begin : gen_meta
                localparam int H_META = (r*EXTENDED_META_WIDTH) + EXTENDED_META_WIDTH - 1;
                localparam int L_META = (r*EXTENDED_META_WIDTH) + TS_WIDTH;
                assign meta[(r+1)*META_WIDTH-1 : r*META_WIDTH] = mfb_rx.META[H_META : L_META];
            end

            if (TS_WIDTH > 0) begin : gen_ts
                localparam int H_TS = (r*EXTENDED_META_WIDTH) + TS_WIDTH - 1;
                localparam int L_TS = (r*EXTENDED_META_WIDTH);
                assign timestamp[(r+1)*TS_WIDTH-1 : r*TS_WIDTH] = mfb_rx.META[H_TS : L_TS];
            end
        end
    endgenerate

    MFB_PACKET_DELAYER #(
        .MFB_REGIONS        (REGIONS),
        .MFB_REGION_SIZE    (REGION_SIZE),
        .MFB_BLOCK_SIZE     (BLOCK_SIZE),
        .MFB_ITEM_WIDTH     (ITEM_WIDTH),
        .MFB_META_WIDTH     (META_WIDTH),

        .TS_WIDTH           (TS_WIDTH),
        .TS_FORMAT          (TS_FORMAT),
        .FIFO_DEPTH         (FIFO_DEPTH),
        .FIFO_AF_OFFSET     (FIFO_AF_OFFSET),
        .FIFO_AE_OFFSET     (FIFO_AE_OFFSET)
    ) VHDL_DUT_U (
        .CLK        (CLK),
        .RESET      (RST),

        .TIME_RESET (TIME_RESET),
        .CURRENT_TIME(CURRENT_TIME),
        .PAUSE_REQUEST (PAUSE_REQUEST),
        //RX inf
        .RX_MFB_DATA    (mfb_rx.DATA),
        .RX_MFB_META    (meta),
        .RX_MFB_TS      (timestamp),
        .RX_MFB_SOF_POS (mfb_rx.SOF_POS),
        .RX_MFB_EOF_POS (mfb_rx.EOF_POS),
        .RX_MFB_SOF     (mfb_rx.SOF),
        .RX_MFB_EOF     (mfb_rx.EOF),
        .RX_MFB_SRC_RDY (mfb_rx.SRC_RDY),
        .RX_MFB_DST_RDY (mfb_rx.DST_RDY),
        //TX inf
        .TX_MFB_DATA    (mfb_tx.DATA),
        .TX_MFB_META    (mfb_tx.META),
        .TX_MFB_SOF_POS (mfb_tx.SOF_POS),
        .TX_MFB_EOF_POS (mfb_tx.EOF_POS),
        .TX_MFB_SOF     (mfb_tx.SOF),
        .TX_MFB_EOF     (mfb_tx.EOF),
        .TX_MFB_SRC_RDY (mfb_tx.SRC_RDY),
        .TX_MFB_DST_RDY (mfb_tx.DST_RDY)

    );


endmodule
