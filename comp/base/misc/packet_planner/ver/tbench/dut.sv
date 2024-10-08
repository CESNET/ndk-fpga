//-- dut.sv: Design Under Test.
//-- Copyright (C) 2020 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import test_pkg::*;

module DUT (
    input logic CLK,
    input logic RESET,
    iMvbRx.dut  RX_STREAMS [NUMBER_OF_STREAMS],
    iMvbTx.dut  TX_STREAMS [NUMBER_OF_STREAMS],
    iMvbTx.dut  TX_GLOBAL,
    iPtr.dut    PTR_INT
);
    // -- Declaring logic needed to connect read and write pointers
    logic [SPACE_GLB_PTR-1:0]    space_glb_wr_ptr;
    logic [SPACE_GLB_PTR-1:0]    space_glb_rd_ptr;

    // -- Declaring logic needed to connect RX_STREAMS interfaces to DUT
    logic [NUMBER_OF_PACKETS-1:0]   mvb_rx_stream_vld       [NUMBER_OF_STREAMS-1:0];
    logic [NUMBER_OF_STREAMS-1:0]   mvb_rx_stream_src_rdy;
    logic [NUMBER_OF_STREAMS-1:0]   mvb_rx_stream_afull;
    logic [META_WIDTH-1:0]          mvb_rx_stream_meta      [NUMBER_OF_STREAMS-1:0][NUMBER_OF_PACKETS-1:0];
    logic [LEN-1:0]                 mvb_rx_stream_len       [NUMBER_OF_STREAMS-1:0][NUMBER_OF_PACKETS-1:0];

    // -- Declaring logic needed to connect TX_STREAMS interfaces to DUT
    logic [META_WIDTH-1:0]          mvb_tx_stream_meta      [NUMBER_OF_STREAMS-1:0][NUMBER_OF_PACKETS-1:0];
    logic [LEN-1:0]                 mvb_tx_stream_len       [NUMBER_OF_STREAMS-1:0][NUMBER_OF_PACKETS-1:0];
    logic [ADDRES_WIDTH-1:0]        mvb_tx_stream_addr      [NUMBER_OF_STREAMS-1:0][NUMBER_OF_PACKETS-1:0];
    logic [NUMBER_OF_PACKETS-1:0]   mvb_tx_stream_vld       [NUMBER_OF_STREAMS-1:0];
    logic [NUMBER_OF_PACKETS-1:0]   mvb_tx_stream_dst_rdy   [NUMBER_OF_STREAMS-1:0];
    logic [NUMBER_OF_STREAMS-1:0]   mvb_tx_stream_afull;

    // -- Declaring logic needed to connect TX_GLOBAL interface to DUT
    logic [META_WIDTH-1:0]          mvb_tx_global_meta      [PACKETS_IN_ONE_STEP-1:0];
    logic [LEN-1:0]                 mvb_tx_global_len       [PACKETS_IN_ONE_STEP-1:0];
    logic [ADDRES_WIDTH-1:0]        mvb_tx_global_addr      [PACKETS_IN_ONE_STEP-1:0];
    logic [PACKETS_IN_ONE_STEP-1:0] mvb_tx_global_dst_rdy;
    logic [PACKETS_IN_ONE_STEP-1:0] mvb_tx_global_vld;
    logic                           mvb_tx_global_afull;

    // -- Assigning interfaces to logic
    generate
        if(STREAM_OUTPUT_EN == 1 && GLOBAL_OUTPUT_EN == 0)begin
            // -- If only the steam output is enabled, then connect space_glb_rd_ptr to space_glb_we_ptr
            assign space_glb_rd_ptr = space_glb_wr_ptr;
        end else begin
            // -- In other situations the separed process changing space_glb_rd_ptr
            assign space_glb_rd_ptr = PTR_INT.SPACE_GLB_RD_PTR;
            assign PTR_INT.SPACE_GLB_WR_PTR = space_glb_wr_ptr;
        end
        for (genvar i = 0 ; i < NUMBER_OF_STREAMS ; i++ ) begin
            // -- Assigning interface RX_STREAM
            assign mvb_rx_stream_src_rdy[i] = ~mvb_rx_stream_afull[i] && RX_STREAMS[i].SRC_RDY;
            assign RX_STREAMS[i].DST_RDY    = ~mvb_rx_stream_afull[i];

            for (genvar z = 0 ; z < NUMBER_OF_PACKETS ; z++) begin
                assign mvb_rx_stream_vld[i][z]  = RX_STREAMS[i].VLD[z] && RX_STREAMS[i].SRC_RDY;
                assign mvb_rx_stream_meta[i][z] = RX_STREAMS[i].DATA[RX_ITEM_WIDTH*(1+z)-1:LEN+z*RX_ITEM_WIDTH];
                assign mvb_rx_stream_len[i][z]  = RX_STREAMS[i].DATA[LEN-1+z*RX_ITEM_WIDTH:z*RX_ITEM_WIDTH];
            end

            // -- Assigning interface TX_STREAMS
            for (genvar z = 0 ; z < NUMBER_OF_PACKETS ; z++) begin
                assign TX_STREAMS[i].DATA[TX_ITEM_WIDTH*z + META_WIDTH + ADDRES_WIDTH+LEN-1 -: META_WIDTH] = mvb_tx_stream_meta[i][z];
                assign TX_STREAMS[i].DATA[TX_ITEM_WIDTH*z + ADDRES_WIDTH+LEN-1 -: LEN]                     = mvb_tx_stream_len[i][z];
                assign TX_STREAMS[i].DATA[TX_ITEM_WIDTH*z + ADDRES_WIDTH-1 -: ADDRES_WIDTH]                = mvb_tx_stream_addr[i][z];
                if(STREAM_OUTPUT_AFULL==0) begin
                    // -- Assigning bit DST_RDY of the interface to all TX_STR_PKT_DST_RDY bits
                    assign mvb_tx_stream_dst_rdy[i][z] = TX_STREAMS[i].DST_RDY;
                end
            end
            assign TX_STREAMS[i].VLD        = mvb_tx_stream_vld[i];
            assign TX_STREAMS[i].SRC_RDY    = |mvb_tx_stream_vld[i];
            if (STREAM_OUTPUT_AFULL == 1) begin
                // -- Assigning bit DST_RDY to TX_STR_PKT_AFULL
                assign mvb_tx_stream_afull[i] = !TX_STREAMS[i].DST_RDY;
            end
        end

        // -- Assigning interface TX_GLOBAL
        for ( genvar z = 0 ; z < PACKETS_IN_ONE_STEP ; z++ ) begin
            assign TX_GLOBAL.DATA[TX_GLOBAL_ITEM_WIDTH*(1+z)-1:ADDRES_WIDTH+LEN+z*TX_GLOBAL_ITEM_WIDTH]             = mvb_tx_global_meta[z];
            assign TX_GLOBAL.DATA[LEN+ADDRES_WIDTH-1+z*TX_GLOBAL_ITEM_WIDTH:ADDRES_WIDTH+z*TX_GLOBAL_ITEM_WIDTH]    = mvb_tx_global_len[z];
            assign TX_GLOBAL.DATA[ADDRES_WIDTH-1+z*TX_GLOBAL_ITEM_WIDTH:z*TX_GLOBAL_ITEM_WIDTH]                     = mvb_tx_global_addr[z];
            if(GLOBAL_OUTPUT_AFULL == 0) begin
                // -- Assigning bit DST_RDY of the interface to all TX_GLB_PKT_DST_RDY bits
                assign mvb_tx_global_dst_rdy[z] = TX_GLOBAL.DST_RDY;
            end
        end
        assign TX_GLOBAL.VLD        = mvb_tx_global_vld;
        assign TX_GLOBAL.SRC_RDY    = |mvb_tx_global_vld;
        if(GLOBAL_OUTPUT_AFULL==1) begin
            // -- Assigning bit DST_RDY to TX_GLB_PKT_AFULL
            assign mvb_tx_global_afull = !TX_GLOBAL.DST_RDY;
        end

    endgenerate

    PACKET_PLANNER #(
        .STREAMS           (NUMBER_OF_STREAMS),
        .PKTS              (NUMBER_OF_PACKETS),
        .PLANNED_PKTS      (PACKETS_IN_ONE_STEP),
        .METADATA_WIDTH    (META_WIDTH),
        .SPACE_SIZE        (SPACE_SIZE),
        .PKT_SIZE          (PACKET_SIZE),
        .GAP_SIZE          (GAP_SIZE),
        .GAP_SIZE_MIN      (MINIMAL_GAP_SIZE),
        .ALIGN             (ADRESS_ALIGNMENT),
        .FIFO_ITEMS        (FIFO_ITEMS),
        .FIFO_AFULL_OFFSET (FIFO_AFULL),
        .STREAM_OUT_EN     (STREAM_OUTPUT_EN),
        .GLOBAL_OUT_EN     (GLOBAL_OUTPUT_EN),
        .STREAM_OUT_AFULL  (STREAM_OUTPUT_AFULL),
        .GLOBAL_OUT_AFULL  (GLOBAL_OUTPUT_AFULL)
    ) VHDL_DUT_U (
        .CLK                (CLK),
        .RESET              (RESET),
        .RX_STR_PKT_META    (mvb_rx_stream_meta),
        .RX_STR_PKT_LEN     (mvb_rx_stream_len),
        .RX_STR_PKT_VLD     (mvb_rx_stream_vld),
        .RX_STR_PKT_SRC_RDY (mvb_rx_stream_src_rdy),
        .RX_STR_PKT_AFULL   (mvb_rx_stream_afull),
        .SPACE_GLB_RD_PTR   (space_glb_rd_ptr),
        .SPACE_GLB_WR_PTR   (space_glb_wr_ptr),
        .TX_STR_PKT_META    (mvb_tx_stream_meta),
        .TX_STR_PKT_LEN     (mvb_tx_stream_len),
        .TX_STR_PKT_ADDR    (mvb_tx_stream_addr),
        .TX_STR_PKT_VLD     (mvb_tx_stream_vld),
        .TX_STR_PKT_DST_RDY (mvb_tx_stream_dst_rdy),
        .TX_STR_PKT_AFULL   (mvb_tx_stream_afull),
        .TX_GLB_PKT_META    (mvb_tx_global_meta),
        .TX_GLB_PKT_LEN     (mvb_tx_global_len),
        .TX_GLB_PKT_ADDR    (mvb_tx_global_addr),
        .TX_GLB_PKT_VLD     (mvb_tx_global_vld),
        .TX_GLB_PKT_DST_RDY (mvb_tx_global_dst_rdy),
        .TX_GLB_PKT_AFULL   (mvb_tx_global_afull)
    );

endmodule
