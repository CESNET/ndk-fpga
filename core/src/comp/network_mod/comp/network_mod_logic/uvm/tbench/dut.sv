// dut.sv: Design under test 
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kondys <xkondy00@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause 

import test::*;

module DUT (
    input logic                           CLK_USER,
    input logic                           CLK_CORE,
    input logic [RESET_USER_WIDTH-1:0]    RESET_USER,
    input logic [RESET_CORE_WIDTH-1:0]    RESET_CORE,
    input logic                           MI_CLK,

    // TX path
    mfb_if.dut_rx   user_mfb_rx,
    mfb_if.dut_tx   core_mfb_tx[ETH_CHANNELS],
    // RX path
    mfb_if.dut_rx   core_mfb_rx[ETH_CHANNELS],
    mfb_if.dut_tx   user_mfb_tx,
    mvb_if.dut_tx   user_mvb_tx,

    // MVB interface for RX MAC Lite DISCARD
    mvb_if.dut_tx   mvb_discard[ETH_CHANNELS],

    mi_if.dut_slave mi_config
    );

    localparam CORE_DATA_W    = CORE_REGIONS*CORE_REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH;
    localparam CORE_SOF_POS_W = CORE_REGIONS*$clog2(CORE_REGION_SIZE);
    localparam CORE_EOF_POS_W = CORE_REGIONS*$clog2(CORE_REGION_SIZE*BLOCK_SIZE);

    // TX of CORE side
    logic [CORE_DATA_W   -1:0]         tx_mfb_data    [ETH_CHANNELS-1:0];
    logic [CORE_REGIONS  -1:0]         tx_mfb_sof     [ETH_CHANNELS-1:0];
    logic [CORE_REGIONS  -1:0]         tx_mfb_eof     [ETH_CHANNELS-1:0];
    logic [CORE_SOF_POS_W-1:0]         tx_mfb_sof_pos [ETH_CHANNELS-1:0];
    logic [CORE_EOF_POS_W-1:0]         tx_mfb_eof_pos [ETH_CHANNELS-1:0];
    logic [ETH_CHANNELS  -1:0]         tx_mfb_src_rdy;
    logic [ETH_CHANNELS  -1:0]         tx_mfb_dst_rdy;

    // RX of CORE side
    logic [CORE_DATA_W   -1:0]         rx_mfb_data    [ETH_CHANNELS-1:0];
    logic [CORE_REGIONS  -1:0]         rx_mfb_sof     [ETH_CHANNELS-1:0];
    logic [CORE_REGIONS  -1:0]         rx_mfb_eof     [ETH_CHANNELS-1:0];
    logic [CORE_SOF_POS_W-1:0]         rx_mfb_sof_pos [ETH_CHANNELS-1:0];
    logic [CORE_EOF_POS_W-1:0]         rx_mfb_eof_pos [ETH_CHANNELS-1:0];
    logic [CORE_REGIONS  -1:0]         rx_mfb_error   [ETH_CHANNELS-1:0];
    logic [ETH_CHANNELS  -1:0]         rx_mfb_src_rdy;

    // MVB discard
    logic [RX_MAC_LITE_REGIONS-1:0]    mvb_data[ETH_CHANNELS-1:0];
    logic [RX_MAC_LITE_REGIONS-1:0]    mvb_vld [ETH_CHANNELS-1:0];


    generate

        for (genvar i = 0; i < ETH_CHANNELS; i++) begin
            assign core_mfb_tx[i].DATA    = tx_mfb_data[i];
            assign core_mfb_tx[i].SOF     = tx_mfb_sof[i];
            assign core_mfb_tx[i].EOF     = tx_mfb_eof[i];
            assign core_mfb_tx[i].SOF_POS = tx_mfb_sof_pos[i];
            assign core_mfb_tx[i].EOF_POS = tx_mfb_eof_pos[i];
            assign core_mfb_tx[i].SRC_RDY = tx_mfb_src_rdy[i];
            assign tx_mfb_dst_rdy[i] = core_mfb_tx[i].DST_RDY;

            assign rx_mfb_data[i]    = core_mfb_rx[i].DATA;
            assign rx_mfb_sof[i]     = core_mfb_rx[i].SOF;
            assign rx_mfb_eof[i]     = core_mfb_rx[i].EOF;
            assign rx_mfb_sof_pos[i] = core_mfb_rx[i].SOF_POS;
            assign rx_mfb_eof_pos[i] = core_mfb_rx[i].EOF_POS;
            assign rx_mfb_error[i]   = 1'b0;
            assign rx_mfb_src_rdy[i] = core_mfb_rx[i].SRC_RDY;
            assign core_mfb_rx[i].DST_RDY = 1'b1;

            assign mvb_discard[i].DATA    = mvb_data[i];
            assign mvb_discard[i].VLD     = mvb_vld[i];
            assign mvb_discard[i].SRC_RDY = |mvb_vld[i];
            assign mvb_discard[i].DST_RDY = 1;
        end

    endgenerate

    NETWORK_MOD_LOGIC #(
        .ETH_PORT_CHAN      (ETH_CHANNELS),
        .ETH_PORT_ID        (ETH_PORT_ID),
        .USER_REGIONS       (USER_REGIONS),
        .USER_REGION_SIZE   (USER_REGION_SIZE),
        .CORE_REGIONS       (CORE_REGIONS),
        .CORE_REGION_SIZE   (CORE_REGION_SIZE),
        .BLOCK_SIZE         (BLOCK_SIZE),
        .ITEM_WIDTH         (ITEM_WIDTH),
        .MI_DATA_WIDTH      (MI_DATA_WIDTH),
        .MI_ADDR_WIDTH      (MI_ADDR_WIDTH),
        .RESET_USER_WIDTH   (RESET_USER_WIDTH),
        .RESET_CORE_WIDTH   (RESET_CORE_WIDTH),
        .RESIZE_BUFFER      (RESIZE_BUFFER),
        .DEVICE             (DEVICE),
        .BOARD              (BOARD)
    ) VHDL_DUT_U (
        .CLK_USER                (CLK_USER),
        .CLK_CORE                (CLK_CORE),
        .RESET_USER              (RESET_USER),
        .RESET_CORE              (RESET_CORE),

        // TX path ------------------------------------
        // User side
        .RX_USER_MFB_DATA        (user_mfb_rx.DATA),
        .RX_USER_MFB_HDR         (user_mfb_rx.META),
        .RX_USER_MFB_SOF_POS     (user_mfb_rx.SOF_POS),
        .RX_USER_MFB_EOF_POS     (user_mfb_rx.EOF_POS),
        .RX_USER_MFB_SOF         (user_mfb_rx.SOF),
        .RX_USER_MFB_EOF         (user_mfb_rx.EOF),
        .RX_USER_MFB_SRC_RDY     (user_mfb_rx.SRC_RDY),
        .RX_USER_MFB_DST_RDY     (user_mfb_rx.DST_RDY),
        // Core side
        .TX_CORE_MFB_DATA        (tx_mfb_data),
        .TX_CORE_MFB_SOF_POS     (tx_mfb_sof_pos),
        .TX_CORE_MFB_EOF_POS     (tx_mfb_eof_pos),
        .TX_CORE_MFB_SOF         (tx_mfb_sof),
        .TX_CORE_MFB_EOF         (tx_mfb_eof),
        .TX_CORE_MFB_SRC_RDY     (tx_mfb_src_rdy),
        .TX_CORE_MFB_DST_RDY     (tx_mfb_dst_rdy),

        // RX path ------------------------------------
        // Core side
        .RX_CORE_MFB_DATA        (rx_mfb_data),
        .RX_CORE_MFB_SOF_POS     (rx_mfb_sof_pos),
        .RX_CORE_MFB_EOF_POS     (rx_mfb_eof_pos),
        .RX_CORE_MFB_SOF         (rx_mfb_sof),
        .RX_CORE_MFB_EOF         (rx_mfb_eof),
        .RX_CORE_MFB_ERROR       (rx_mfb_error),
        .RX_CORE_MFB_SRC_RDY     (rx_mfb_src_rdy),
        // User side
        .TX_USER_MFB_DATA        (user_mfb_tx.DATA),
        .TX_USER_MFB_SOF_POS     (user_mfb_tx.SOF_POS),
        .TX_USER_MFB_EOF_POS     (user_mfb_tx.EOF_POS),
        .TX_USER_MFB_SOF         (user_mfb_tx.SOF),
        .TX_USER_MFB_EOF         (user_mfb_tx.EOF),
        .TX_USER_MFB_SRC_RDY     (user_mfb_tx.SRC_RDY),
        .TX_USER_MFB_DST_RDY     (user_mfb_tx.DST_RDY),

        .TX_USER_MVB_DATA        (user_mvb_tx.DATA),
        .TX_USER_MVB_VLD         (user_mvb_tx.VLD),
        .TX_USER_MVB_SRC_RDY     (user_mvb_tx.SRC_RDY),
        .TX_USER_MVB_DST_RDY     (user_mvb_tx.DST_RDY),

        // MI -----------------------------------------
        .MI_CLK                  (MI_CLK),
        .MI_RESET                (1'b0),
        .MI_DWR                  (mi_config.DWR),
        .MI_ADDR                 (mi_config.ADDR),
        .MI_RD                   (mi_config.RD),
        .MI_WR                   (mi_config.WR),
        .MI_BE                   (mi_config.BE),
        .MI_DRD                  (mi_config.DRD),
        .MI_ARDY                 (mi_config.ARDY),
        .MI_DRDY                 (mi_config.DRDY)
    );

    // MVB discard inf --------------------------------
    generate
        for (genvar j = 0; j < ETH_CHANNELS; j++) begin
            assign  mvb_data[j] = VHDL_DUT_U.rx_g[j].rx_mac_g.rx_mac_i.s_stin_discarded;
            assign  mvb_vld[j]  = VHDL_DUT_U.rx_g[j].rx_mac_g.rx_mac_i.s_stin_valid;
        end
    endgenerate
    

endmodule
