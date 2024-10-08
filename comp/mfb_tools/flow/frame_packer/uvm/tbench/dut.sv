// dut.sv: Design under test
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): David Beneš <xbenes52@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

import test::*;

module DUT (
    input logic     CLK,
    input logic     RST,
    mfb_if.dut_rx   mfb_rx,
    mvb_if.dut_rx   mvb_rx,
    mfb_if.dut_tx   mfb_tx,
    mvb_if.dut_tx   mvb_tx
    );

    localparam RX_MVB_ITEM_WIDTH = $clog2(RX_CHANNELS) + $clog2(USR_RX_PKT_SIZE_MAX+1);
    localparam TX_MVB_ITEM_WIDTH = $clog2(RX_CHANNELS) + $clog2(USR_RX_PKT_SIZE_MAX+1) + HDR_META_WIDTH + 1;
    localparam MVB_LEN_WIDTH = $clog2(USR_RX_PKT_SIZE_MAX+1);
    localparam MVB_CHANNEL_WIDTH = $clog2(RX_CHANNELS);

    logic [MFB_REGIONS*MVB_LEN_WIDTH-1:0]     rx_mvb_len;
    logic [MFB_REGIONS*MVB_CHANNEL_WIDTH-1:0] rx_mvb_channel;

    logic [MFB_REGIONS*MVB_LEN_WIDTH-1:0]     tx_mvb_len;
    logic [MFB_REGIONS*HDR_META_WIDTH-1:0]    tx_mvb_hdr_meta;
    logic [MFB_REGIONS*MVB_CHANNEL_WIDTH-1:0] tx_mvb_channel;
    logic [MFB_REGIONS-1:0]                   tx_mvb_discard;

    wire [MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1:0]    buffer_data;
    wire [MFB_REGIONS-1 : 0]                                                buffer_sof;
    wire [MFB_REGIONS-1 : 0]                                                buffer_eof;
    wire [MFB_REGIONS*$clog2(MFB_REGION_SIZE)-1 : 0]                        buffer_sof_pos;
    wire [MFB_REGIONS*$clog2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 : 0]         buffer_eof_pos;
    wire logic buffer_src_rdy;
    wire logic buffer_dst_rdy;

    wire [MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1:0]    pipe_data;
    wire [MFB_REGIONS-1 : 0]                                                pipe_sof;
    wire [MFB_REGIONS-1 : 0]                                                pipe_eof;
    wire [MFB_REGIONS*$clog2(MFB_REGION_SIZE)-1 : 0]                        pipe_sof_pos;
    wire [MFB_REGIONS*$clog2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 : 0]         pipe_eof_pos;
    wire logic pipe_src_rdy;
    wire logic pipe_dst_rdy;

    generate
        for (genvar r = 0; r < MFB_REGIONS; r++) begin
            assign {rx_mvb_len[(r+1)*MVB_LEN_WIDTH-1 -: MVB_LEN_WIDTH], rx_mvb_channel  [(r+1)*MVB_CHANNEL_WIDTH-1 -: MVB_CHANNEL_WIDTH]} = mvb_rx.DATA[(r+1)*(RX_MVB_ITEM_WIDTH)-1 -: RX_MVB_ITEM_WIDTH];
        end
    endgenerate

    generate
        for (genvar r = 0; r < MFB_REGIONS; r++) begin
            // Discard
            assign mvb_tx.DATA[(r+1)*(TX_MVB_ITEM_WIDTH)-1 -: TX_MVB_ITEM_WIDTH] = {tx_mvb_len      [(r+1)*MVB_LEN_WIDTH-1 : r*MVB_LEN_WIDTH],
                                                                              tx_mvb_hdr_meta [(r+1)*HDR_META_WIDTH-1 : r*HDR_META_WIDTH],
                                                                              tx_mvb_discard  [r],
                                                                              tx_mvb_channel  [(r+1)*MVB_CHANNEL_WIDTH-1 : r*MVB_CHANNEL_WIDTH]};
        end
    endgenerate

    // assign mvb_tx.DATA = {tx_mvb_len, tx_mvb_hdr_meta, tx_mvb_channel, tx_mvb_discard};
    //1 region:
    // generate
    //     if (MVB_CHANNEL_WIDTH != 0) begin
    //         assign mvb_tx.DATA = {tx_mvb_len, tx_mvb_hdr_meta, tx_mvb_channel, tx_mvb_discard};
    //     end else begin
    //         assign mvb_tx.DATA = {tx_mvb_len, tx_mvb_hdr_meta, tx_mvb_discard};
    //     end
    // endgenerate
    //assign mvb_tx.DATA = {tx_mvb_discard, tx_mvb_channel, tx_mvb_hdr_meta, tx_mvb_len};

    MFB_FIFOX # (
        .REGIONS             (MFB_REGIONS),
        .REGION_SIZE         (MFB_REGION_SIZE),
        .BLOCK_SIZE          (MFB_BLOCK_SIZE),
        .ITEM_WIDTH          (MFB_ITEM_WIDTH),

        .FIFO_DEPTH          (16),
        .ALMOST_FULL_OFFSET  (8)
    ) BUFFER_I (

        .CLK            (CLK),
        .RST            (RST),

        .RX_DATA        (mfb_rx.DATA),
        .RX_SOF         (mfb_rx.SOF),
        .RX_EOF         (mfb_rx.EOF),
        .RX_SOF_POS     (mfb_rx.SOF_POS),
        .RX_EOF_POS     (mfb_rx.EOF_POS),
        .RX_SRC_RDY     (mfb_rx.SRC_RDY),
        .RX_DST_RDY     (mfb_rx.DST_RDY),

        .TX_DATA        (buffer_data),
        .TX_SOF         (buffer_sof),
        .TX_EOF         (buffer_eof),
        .TX_SOF_POS     (buffer_sof_pos),
        .TX_EOF_POS     (buffer_eof_pos),
        .TX_SRC_RDY     (buffer_src_rdy),
        .TX_DST_RDY     (buffer_dst_rdy),

        .FIFO_STATUS    (),
        .FIFO_AFULL     (),
        .FIFO_AEMPTY    ()
    );

    MFB_PIPE # (
        .REGIONS        (MFB_REGIONS),
        .REGION_SIZE    (MFB_REGION_SIZE),
        .BLOCK_SIZE     (MFB_BLOCK_SIZE),
        .ITEM_WIDTH     (MFB_ITEM_WIDTH)
    ) DELAY_I (
        .CLK    (CLK),
        .RESET  (RST),
        .RX_DATA        (buffer_data),
        .RX_SOF         (buffer_sof),
        .RX_EOF         (buffer_eof),
        .RX_SOF_POS     (buffer_sof_pos),
        .RX_EOF_POS     (buffer_eof_pos),
        .RX_SRC_RDY     (buffer_src_rdy),
        .RX_DST_RDY     (buffer_dst_rdy),

        .TX_DATA        (pipe_data),
        .TX_SOF         (pipe_sof),
        .TX_EOF         (pipe_eof),
        .TX_SOF_POS     (pipe_sof_pos),
        .TX_EOF_POS     (pipe_eof_pos),
        .TX_SRC_RDY     (pipe_src_rdy),
        .TX_DST_RDY     (pipe_dst_rdy)

    );

    FRAME_PACKER # (
        .MFB_REGIONS            (MFB_REGIONS),
        .MFB_REGION_SIZE        (MFB_REGION_SIZE),
        .MFB_BLOCK_SIZE         (MFB_BLOCK_SIZE),
        .MFB_ITEM_WIDTH         (MFB_ITEM_WIDTH),
        .RX_CHANNELS            (RX_CHANNELS),
        .HDR_META_WIDTH         (HDR_META_WIDTH),
        .USR_RX_PKT_SIZE_MAX    (USR_RX_PKT_SIZE_MAX),
        .USR_RX_PKT_SIZE_MIN    (USR_RX_PKT_SIZE_MIN),
        .SPKT_SIZE_MIN          (SPKT_SIZE_MIN),
        .TIMEOUT_CLK_NO         (TIMEOUT_CLK_NO)

    ) VHDL_DUT_U (

        .CLK (CLK),
        .RST (RST),

        .RX_MFB_DATA     (pipe_data),
        .RX_MFB_SOF      (pipe_sof),
        .RX_MFB_EOF      (pipe_eof),
        .RX_MFB_SOF_POS  (pipe_sof_pos),
        .RX_MFB_EOF_POS  (pipe_eof_pos),
        .RX_MFB_SRC_RDY  (pipe_src_rdy),
        .RX_MFB_DST_RDY  (pipe_dst_rdy),

        .RX_MVB_LEN      (rx_mvb_len),
        // .RX_MVB_HDR_META (rx_mvb_hdr_meta),
        .RX_MVB_CHANNEL  (rx_mvb_channel),
        // .RX_MVB_DISCARD  (rx_mvb_discard),
        .RX_MVB_VLD      (mvb_rx.VLD),
        .RX_MVB_SRC_RDY  (mvb_rx.SRC_RDY),
        .RX_MVB_DST_RDY  (mvb_rx.DST_RDY),

        .TX_MFB_DATA     (mfb_tx.DATA),
        .TX_MFB_SOF      (mfb_tx.SOF),
        .TX_MFB_EOF      (mfb_tx.EOF),
        .TX_MFB_SOF_POS  (mfb_tx.SOF_POS),
        .TX_MFB_EOF_POS  (mfb_tx.EOF_POS),
        .TX_MFB_SRC_RDY  (mfb_tx.SRC_RDY),
        .TX_MFB_DST_RDY  (mfb_tx.DST_RDY),

        .TX_MVB_LEN      (tx_mvb_len),
        .TX_MVB_HDR_META (tx_mvb_hdr_meta),
        .TX_MVB_CHANNEL  (tx_mvb_channel),
        .TX_MVB_DISCARD  (tx_mvb_discard),
        .TX_MVB_VLD      (mvb_tx.VLD),
        .TX_MVB_SRC_RDY  (mvb_tx.SRC_RDY),
        .TX_MVB_DST_RDY  (mvb_tx.DST_RDY)

    );


endmodule
