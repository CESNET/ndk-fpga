/*
 * file       : testbench.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: testbench
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`include "uvm_macros.svh"
import uvm_pkg::*;


module testbench;

    /////////////////////////
    // PARAMETRIZE TESTS 
    typedef test::base#(test_pkg::ETH_STREAMS, test_pkg::ETH_CHANNELS, test_pkg::ETH_PKT_MTU, test_pkg::ETH_RX_HDR_WIDTH, test_pkg::ETH_TX_HDR_WIDTH, test_pkg::DMA_STREAMS, test_pkg::DMA_RX_CHANNELS, test_pkg::DMA_TX_CHANNELS, test_pkg::DMA_HDR_META_WIDTH, test_pkg::DMA_PKT_MTU,
                        test_pkg::REGIONS, test_pkg::MFB_REG_SIZE, test_pkg::MFB_BLOCK_SIZE, test_pkg::MFB_ITEM_WIDTH, test_pkg::MEM_PORTS, test_pkg::MEM_ADDR_WIDTH, test_pkg::MEM_BURST_WIDTH, test_pkg::MEM_DATA_WIDTH, test_pkg::MI_DATA_WIDTH, test_pkg::MI_ADDR_WIDTH)
                        test_base;

    typedef test::full_speed#(test_pkg::ETH_STREAMS, test_pkg::ETH_CHANNELS, test_pkg::ETH_PKT_MTU, test_pkg::ETH_RX_HDR_WIDTH, test_pkg::ETH_TX_HDR_WIDTH, test_pkg::DMA_STREAMS, test_pkg::DMA_RX_CHANNELS, test_pkg::DMA_TX_CHANNELS, test_pkg::DMA_HDR_META_WIDTH, test_pkg::DMA_PKT_MTU,
                        test_pkg::REGIONS, test_pkg::MFB_REG_SIZE, test_pkg::MFB_BLOCK_SIZE, test_pkg::MFB_ITEM_WIDTH, test_pkg::MEM_PORTS, test_pkg::MEM_ADDR_WIDTH, test_pkg::MEM_BURST_WIDTH, test_pkg::MEM_DATA_WIDTH, test_pkg::MI_DATA_WIDTH, test_pkg::MI_ADDR_WIDTH)
                        test_full_speed;

    /////////////////////////
    // DEFINE CLOCK
    logic CLK_USER_X1 = 0;
    logic CLK_USER_X2 = 0;
    logic CLK_USER_X3 = 0;
    logic CLK_USER_X4 = 0;

    logic MI_CLK;
    logic DMA_CLK_X1;
    logic DMA_CLK_X2;
    logic APP_CLK;
    logic MEM_CLK = '0;
    logic [test_pkg::MEM_PORTS-1:0] clk_logic_mem;
    //logic [test_pkg::MEM_PORTS-1:0] MEM_CLK = '0;

    /////////////////////////
    // INTERFACESS
    // INPUT INTERFACE
    reset_if     reset_user_x1(CLK_USER_X1);
    reset_if     reset_user_x2(CLK_USER_X2);
    reset_if     reset_user_x3(CLK_USER_X3);
    reset_if     reset_user_x4(CLK_USER_X4);
       // OUTPUT INTERFACE
    reset_if     reset_mi(MI_CLK);
    reset_if     reset_dma_x1(DMA_CLK_X1);
    reset_if     reset_dma_x2(DMA_CLK_X2);
    reset_if     reset_app(APP_CLK);
    reset_if     reset_mem[test_pkg::MEM_PORTS](MEM_CLK);

    // ETHERNET I/O INTERFACE
    mvb_if #(test_pkg::REGIONS,   test_pkg::ETH_RX_HDR_WIDTH)                                                    eth_rx_mvb[test_pkg::ETH_STREAMS](APP_CLK, reset_app.RESET);
    mfb_if #(test_pkg::REGIONS, test_pkg::MFB_REG_SIZE, test_pkg::MFB_BLOCK_SIZE, test_pkg::MFB_ITEM_WIDTH, 0) eth_rx_mfb[test_pkg::ETH_STREAMS](APP_CLK, reset_app.RESET);
    mfb_if #(test_pkg::REGIONS, test_pkg::MFB_REG_SIZE, test_pkg::MFB_BLOCK_SIZE, test_pkg::MFB_ITEM_WIDTH, test_pkg::ETH_TX_HDR_WIDTH) eth_tx_mfb[test_pkg::ETH_STREAMS](APP_CLK, reset_app.RESET);
    // DMA I/O INTERFACE
    localparam DMA_RX_MVB_WIDTH = $clog2(test_pkg::DMA_PKT_MTU+1)+test_pkg::DMA_HDR_META_WIDTH+$clog2(test_pkg::DMA_TX_CHANNELS);
    localparam DMA_TX_MVB_WIDTH = $clog2(test_pkg::DMA_PKT_MTU+1)+test_pkg::DMA_HDR_META_WIDTH+$clog2(test_pkg::DMA_RX_CHANNELS) + 1;
    mvb_if #(test_pkg::REGIONS,   DMA_RX_MVB_WIDTH)                                                            dma_rx_mvb[test_pkg::DMA_STREAMS](APP_CLK, reset_dma_x1.RESET);
    mfb_if #(test_pkg::REGIONS, test_pkg::MFB_REG_SIZE, test_pkg::MFB_BLOCK_SIZE, test_pkg::MFB_ITEM_WIDTH, 0) dma_rx_mfb[test_pkg::DMA_STREAMS](APP_CLK, reset_dma_x1.RESET);
    mvb_if #(test_pkg::REGIONS,   DMA_TX_MVB_WIDTH)                                                            dma_tx_mvb[test_pkg::DMA_STREAMS](APP_CLK, reset_dma_x1.RESET);
    mfb_if #(test_pkg::REGIONS, test_pkg::MFB_REG_SIZE, test_pkg::MFB_BLOCK_SIZE, test_pkg::MFB_ITEM_WIDTH, 0) dma_tx_mfb[test_pkg::DMA_STREAMS](APP_CLK, reset_dma_x1.RESET);

    //CONFIGURE INTERFACE
    mi_if#(test_pkg::MI_DATA_WIDTH, test_pkg::MI_ADDR_WIDTH) config_if(MI_CLK);

    /////////////////////////
    // CLOCK GENERATION
    always #(test_pkg::CLK_PERIOD/2)  CLK_USER_X1 = ~CLK_USER_X1;
    always #(test_pkg::CLK_PERIOD/4)  CLK_USER_X2 = ~CLK_USER_X2;
    always #(test_pkg::CLK_PERIOD/6)  CLK_USER_X3 = ~CLK_USER_X3;
    always #(test_pkg::CLK_PERIOD/8)  CLK_USER_X4 = ~CLK_USER_X4;
    //always #(test_pkg::CLK_MEM_PERIOD[mem_it]/2)  MEM_CLK[mem_it] = ~MEM_CLK[mem_it];

    /////////////////////////
    // RESETS
    // INPUT
    logic [test_pkg::RESET_WIDTH-1:0] reset_logic_user_x1;
    logic [test_pkg::RESET_WIDTH-1:0] reset_logic_user_x2;
    logic [test_pkg::RESET_WIDTH-1:0] reset_logic_user_x3;
    logic [test_pkg::RESET_WIDTH-1:0] reset_logic_user_x4;
    assign reset_logic_user_x1 = {test_pkg::RESET_WIDTH{reset_user_x1.RESET}};
    assign reset_logic_user_x2 = {test_pkg::RESET_WIDTH{reset_user_x2.RESET}};
    assign reset_logic_user_x3 = {test_pkg::RESET_WIDTH{reset_user_x3.RESET}};
    assign reset_logic_user_x4 = {test_pkg::RESET_WIDTH{reset_user_x4.RESET}};
    // OUTPUT
    logic [test_pkg::RESET_WIDTH-1:0] reset_logic_mi;
    logic [test_pkg::RESET_WIDTH-1:0] reset_logic_dma_x1;
    logic [test_pkg::RESET_WIDTH-1:0] reset_logic_dma_x2;
    logic [test_pkg::RESET_WIDTH-1:0] reset_logic_app;
    logic [test_pkg::MEM_PORTS-1:0]   reset_logic_mem;
    assign reset_mi.RESET      = reset_logic_mi[0];
    assign reset_dma_x1.RESET  = reset_logic_dma_x1[0];
    assign reset_dma_x2.RESET  = reset_logic_dma_x2[0];
    assign reset_app.RESET     = reset_logic_app[0];

    for (genvar mem_it = 0; mem_it < test_pkg::MEM_PORTS; mem_it++) begin
        assign reset_logic_mem[mem_it] = reset_mem[mem_it].RESET;
        assign clk_logic_mem[mem_it]   = MEM_CLK;
        //always #(test_pkg::CLK_MEM_PERIOD[mem_it]/2)  MEM_CLK[mem_it] = ~MEM_CLK[mem_it];
    end

    /////////////////////////
    // ETH
    /////////////////////////
    // ETH RX
    logic [test_pkg::ETH_STREAMS*test_pkg::REGIONS*test_pkg::ETH_RX_HDR_WIDTH-1:0] eth_rx_mvb_data;
    logic [test_pkg::ETH_STREAMS*test_pkg::REGIONS-1:0]                            eth_rx_mvb_vld;
    logic [test_pkg::ETH_STREAMS-1:0]                                                eth_rx_mvb_dst_rdy;
    logic [test_pkg::ETH_STREAMS-1:0]                                                eth_rx_mvb_src_rdy;
    logic [test_pkg::ETH_STREAMS*test_pkg::REGIONS*test_pkg::MFB_REG_SIZE*test_pkg::MFB_BLOCK_SIZE*test_pkg::MFB_ITEM_WIDTH-1:0] eth_rx_mfb_data;
    logic [test_pkg::ETH_STREAMS*test_pkg::REGIONS-1:0]                                                                          eth_rx_mfb_sof;
    logic [test_pkg::ETH_STREAMS*test_pkg::REGIONS-1:0]                                                                          eth_rx_mfb_eof;
    logic [test_pkg::ETH_STREAMS*test_pkg::REGIONS*$clog2(test_pkg::MFB_REG_SIZE)-1:0]                                           eth_rx_mfb_sof_pos;
    logic [test_pkg::ETH_STREAMS*test_pkg::REGIONS*$clog2(test_pkg::MFB_REG_SIZE*test_pkg::MFB_BLOCK_SIZE)-1:0]                  eth_rx_mfb_eof_pos;
    logic [test_pkg::ETH_STREAMS-1:0]                                                                                                eth_rx_mfb_src_rdy;
    logic [test_pkg::ETH_STREAMS-1:0]                                                                                                eth_rx_mfb_dst_rdy;
    //ETH TX
    logic [test_pkg::ETH_STREAMS*test_pkg::REGIONS*test_pkg::ETH_TX_HDR_WIDTH-1:0]                                               eth_tx_mfb_meta;
    logic [test_pkg::ETH_STREAMS*test_pkg::REGIONS*test_pkg::MFB_REG_SIZE*test_pkg::MFB_BLOCK_SIZE*test_pkg::MFB_ITEM_WIDTH-1:0] eth_tx_mfb_data;
    logic [test_pkg::ETH_STREAMS*test_pkg::REGIONS-1:0]                                                                          eth_tx_mfb_sof;
    logic [test_pkg::ETH_STREAMS*test_pkg::REGIONS-1:0]                                                                          eth_tx_mfb_eof;
    logic [test_pkg::ETH_STREAMS*test_pkg::REGIONS*$clog2(test_pkg::MFB_REG_SIZE)-1:0]                                           eth_tx_mfb_sof_pos;
    logic [test_pkg::ETH_STREAMS*test_pkg::REGIONS*$clog2(test_pkg::MFB_REG_SIZE*test_pkg::MFB_BLOCK_SIZE)-1:0]                  eth_tx_mfb_eof_pos;
    logic [test_pkg::ETH_STREAMS-1:0]                                                                                                eth_tx_mfb_src_rdy;
    logic [test_pkg::ETH_STREAMS-1:0]                                                                                                eth_tx_mfb_dst_rdy;

    for (genvar eth_it = 0; eth_it < test_pkg::ETH_STREAMS; eth_it++) begin
        //ETH RX
        assign eth_rx_mvb_data[(eth_it+1)*test_pkg::REGIONS*test_pkg::ETH_RX_HDR_WIDTH-1 -: test_pkg::REGIONS*test_pkg::ETH_RX_HDR_WIDTH] = eth_rx_mvb[eth_it].DATA;
        assign eth_rx_mvb_vld[(eth_it+1)*test_pkg::REGIONS-1 -: test_pkg::REGIONS]                                                        = eth_rx_mvb[eth_it].VLD;
        assign eth_rx_mvb_src_rdy[eth_it]                                                                                                     = eth_rx_mvb[eth_it].SRC_RDY;
        assign eth_rx_mvb[eth_it].DST_RDY                                                                                                     = eth_rx_mvb_dst_rdy[eth_it];
        assign eth_rx_mfb_data[(eth_it+1)*test_pkg::REGIONS*test_pkg::MFB_REG_SIZE*test_pkg::MFB_BLOCK_SIZE*test_pkg::MFB_ITEM_WIDTH-1 -: test_pkg::REGIONS*test_pkg::MFB_REG_SIZE*test_pkg::MFB_BLOCK_SIZE*test_pkg::MFB_ITEM_WIDTH] = eth_rx_mfb[eth_it].DATA;
        assign eth_rx_mfb_sof[(eth_it+1)*test_pkg::REGIONS-1 -: test_pkg::REGIONS]                                                    = eth_rx_mfb[eth_it].SOF;
        assign eth_rx_mfb_eof[(eth_it+1)*test_pkg::REGIONS-1 -: test_pkg::REGIONS]                                                    = eth_rx_mfb[eth_it].EOF;
        assign eth_rx_mfb_sof_pos[(eth_it+1)*test_pkg::REGIONS*$clog2(test_pkg::MFB_REG_SIZE)-1 -: test_pkg::REGIONS*$clog2(test_pkg::MFB_REG_SIZE)] = eth_rx_mfb[eth_it].SOF_POS;
        assign eth_rx_mfb_eof_pos[(eth_it+1)*test_pkg::REGIONS*$clog2(test_pkg::MFB_REG_SIZE*test_pkg::MFB_BLOCK_SIZE)-1 -: test_pkg::REGIONS*$clog2(test_pkg::MFB_REG_SIZE*test_pkg::MFB_BLOCK_SIZE)] = eth_rx_mfb[eth_it].EOF_POS;
        assign eth_rx_mfb_src_rdy[eth_it]                                                                                                 = eth_rx_mfb[eth_it].SRC_RDY;
        assign eth_rx_mfb[eth_it].DST_RDY                                                                                          = eth_rx_mfb_dst_rdy[eth_it];
        //ETH TX
        assign eth_tx_mfb[eth_it].META     = eth_tx_mfb_meta[(eth_it+1)*test_pkg::REGIONS*test_pkg::ETH_TX_HDR_WIDTH-1 -: test_pkg::REGIONS*test_pkg::ETH_TX_HDR_WIDTH];
        assign eth_tx_mfb[eth_it].DATA     = eth_tx_mfb_data[(eth_it+1)*test_pkg::REGIONS*test_pkg::MFB_REG_SIZE*test_pkg::MFB_BLOCK_SIZE*test_pkg::MFB_ITEM_WIDTH-1 -: test_pkg::REGIONS*test_pkg::MFB_REG_SIZE*test_pkg::MFB_BLOCK_SIZE*test_pkg::MFB_ITEM_WIDTH];
        assign eth_tx_mfb[eth_it].SOF      = eth_tx_mfb_sof[(eth_it+1)*test_pkg::REGIONS-1 -: test_pkg::REGIONS];
        assign eth_tx_mfb[eth_it].EOF      = eth_tx_mfb_eof[(eth_it+1)*test_pkg::REGIONS-1 -: test_pkg::REGIONS];
        assign eth_tx_mfb[eth_it].SOF_POS  = eth_tx_mfb_sof_pos[(eth_it+1)*test_pkg::REGIONS*$clog2(test_pkg::MFB_REG_SIZE)-1 -: test_pkg::REGIONS*$clog2(test_pkg::MFB_REG_SIZE)];
        assign eth_tx_mfb[eth_it].EOF_POS  = eth_tx_mfb_eof_pos[(eth_it+1)*test_pkg::REGIONS*$clog2(test_pkg::MFB_REG_SIZE*test_pkg::MFB_BLOCK_SIZE)-1 -: test_pkg::REGIONS*$clog2(test_pkg::MFB_REG_SIZE*test_pkg::MFB_BLOCK_SIZE)];
        assign eth_tx_mfb[eth_it].SRC_RDY  = eth_tx_mfb_src_rdy[eth_it];
        assign eth_tx_mfb_dst_rdy[eth_it]  = eth_tx_mfb[eth_it].DST_RDY;
    end


    /////////////////////////
    // DMA
    /////////////////////////
    // DMA RX
    logic [test_pkg::DMA_STREAMS*test_pkg::REGIONS*$clog2(test_pkg::DMA_PKT_MTU+1)-1:0]   dma_rx_mvb_len;
    logic [test_pkg::DMA_STREAMS*test_pkg::REGIONS*test_pkg::DMA_HDR_META_WIDTH-1:0]      dma_rx_mvb_hdr_meta;
    logic [test_pkg::DMA_STREAMS*test_pkg::REGIONS*$clog2(test_pkg::DMA_TX_CHANNELS)-1:0] dma_rx_mvb_channel;
    logic [test_pkg::DMA_STREAMS*test_pkg::REGIONS-1:0]                                   dma_rx_mvb_vld;
    logic [test_pkg::DMA_STREAMS-1:0]                                                        dma_rx_mvb_src_rdy;
    logic [test_pkg::DMA_STREAMS-1:0]                                                        dma_rx_mvb_dst_rdy;
    logic [test_pkg::DMA_STREAMS*test_pkg::REGIONS*test_pkg::MFB_REG_SIZE*test_pkg::MFB_BLOCK_SIZE*test_pkg::MFB_ITEM_WIDTH-1:0] dma_rx_mfb_data;
    logic [test_pkg::DMA_STREAMS*test_pkg::REGIONS-1:0]                                                                          dma_rx_mfb_sof;
    logic [test_pkg::DMA_STREAMS*test_pkg::REGIONS-1:0]                                                                          dma_rx_mfb_eof;
    logic [test_pkg::DMA_STREAMS*test_pkg::REGIONS*$clog2(test_pkg::MFB_REG_SIZE)-1:0]                                           dma_rx_mfb_sof_pos;
    logic [test_pkg::DMA_STREAMS*test_pkg::REGIONS*$clog2(test_pkg::MFB_REG_SIZE*test_pkg::MFB_BLOCK_SIZE)-1:0]                  dma_rx_mfb_eof_pos;
    logic [test_pkg::DMA_STREAMS-1:0]                                                                                            dma_rx_mfb_src_rdy;
    logic [test_pkg::DMA_STREAMS-1:0]                                                                                            dma_rx_mfb_dst_rdy;
    //DMA TX
    logic [test_pkg::DMA_STREAMS*test_pkg::REGIONS*$clog2(test_pkg::DMA_PKT_MTU+1)-1:0]   dma_tx_mvb_len;
    logic [test_pkg::DMA_STREAMS*test_pkg::REGIONS*test_pkg::DMA_HDR_META_WIDTH-1:0]      dma_tx_mvb_hdr_meta;
    logic [test_pkg::DMA_STREAMS*test_pkg::REGIONS*$clog2(test_pkg::DMA_RX_CHANNELS)-1:0] dma_tx_mvb_channel;
    logic [test_pkg::DMA_STREAMS*test_pkg::REGIONS-1:0]                                   dma_tx_mvb_discard;
    logic [test_pkg::DMA_STREAMS*test_pkg::REGIONS-1:0]                                   dma_tx_mvb_vld;
    logic [test_pkg::DMA_STREAMS-1:0]                                                       dma_tx_mvb_src_rdy;
    logic [test_pkg::DMA_STREAMS-1:0]                                                       dma_tx_mvb_dst_rdy;
    logic [test_pkg::DMA_STREAMS*test_pkg::REGIONS*test_pkg::MFB_REG_SIZE*test_pkg::MFB_BLOCK_SIZE*test_pkg::MFB_ITEM_WIDTH-1:0] dma_tx_mfb_data;
    logic [test_pkg::DMA_STREAMS*test_pkg::REGIONS-1:0]                                                                          dma_tx_mfb_sof;
    logic [test_pkg::DMA_STREAMS*test_pkg::REGIONS-1:0]                                                                          dma_tx_mfb_eof;
    logic [test_pkg::DMA_STREAMS*test_pkg::REGIONS*$clog2(test_pkg::MFB_REG_SIZE)-1:0]                                           dma_tx_mfb_sof_pos;
    logic [test_pkg::DMA_STREAMS*test_pkg::REGIONS*$clog2(test_pkg::MFB_REG_SIZE*test_pkg::MFB_BLOCK_SIZE)-1:0]                  dma_tx_mfb_eof_pos;
    logic [test_pkg::DMA_STREAMS-1:0]                                                                                            dma_tx_mfb_src_rdy;
    logic [test_pkg::DMA_STREAMS-1:0]                                                                                            dma_tx_mfb_dst_rdy;

    for (genvar dma_it = 0; dma_it < test_pkg::DMA_STREAMS; dma_it++) begin
        //DMA RX
        for (genvar dma_region = 0; dma_region < test_pkg::REGIONS; dma_region++) begin
            assign dma_rx_mvb_len[(dma_it*test_pkg::REGIONS + dma_region + 1)*$clog2(test_pkg::DMA_PKT_MTU+1)-1 -: $clog2(test_pkg::DMA_PKT_MTU+1)]         = dma_rx_mvb[dma_it].DATA[dma_region*DMA_RX_MVB_WIDTH + $clog2(test_pkg::DMA_PKT_MTU+1)-1 -: $clog2(test_pkg::DMA_PKT_MTU+1)];
            assign dma_rx_mvb_hdr_meta[(dma_it*test_pkg::REGIONS + dma_region + 1)*test_pkg::DMA_HDR_META_WIDTH-1 -: test_pkg::DMA_HDR_META_WIDTH]          = dma_rx_mvb[dma_it].DATA[dma_region*DMA_RX_MVB_WIDTH + $clog2(test_pkg::DMA_PKT_MTU+1)+test_pkg::DMA_HDR_META_WIDTH-1 -: test_pkg::DMA_HDR_META_WIDTH];
            assign dma_rx_mvb_channel[(dma_it*test_pkg::REGIONS + dma_region + 1)*$clog2(test_pkg::DMA_RX_CHANNELS)-1 -: $clog2(test_pkg::DMA_RX_CHANNELS)] = dma_rx_mvb[dma_it].DATA[dma_region*DMA_RX_MVB_WIDTH + $clog2(test_pkg::DMA_PKT_MTU+1)+test_pkg::DMA_HDR_META_WIDTH+$clog2(test_pkg::DMA_TX_CHANNELS)-1 -: $clog2(test_pkg::DMA_TX_CHANNELS)];
            assign dma_rx_mvb_vld[dma_it*test_pkg::REGIONS + dma_region]                                                                                    = dma_rx_mvb[dma_it].VLD[dma_region];
        end
        assign dma_rx_mvb_src_rdy[dma_it]  = dma_rx_mvb[dma_it].SRC_RDY;
        assign dma_rx_mvb[dma_it].DST_RDY  = dma_rx_mvb_dst_rdy[dma_it];

        assign dma_rx_mfb_data[(dma_it+1)*test_pkg::REGIONS*test_pkg::MFB_REG_SIZE*test_pkg::MFB_BLOCK_SIZE*test_pkg::MFB_ITEM_WIDTH -1 -: test_pkg::REGIONS*test_pkg::MFB_REG_SIZE*test_pkg::MFB_BLOCK_SIZE*test_pkg::MFB_ITEM_WIDTH]    = dma_rx_mfb[dma_it].DATA;
        assign dma_rx_mfb_sof[(dma_it+1)*test_pkg::REGIONS -1 -: test_pkg::REGIONS]                                                                                 = dma_rx_mfb[dma_it].SOF;
        assign dma_rx_mfb_eof[(dma_it+1)*test_pkg::REGIONS -1 -: test_pkg::REGIONS]                                                                                 = dma_rx_mfb[dma_it].EOF;
        assign dma_rx_mfb_sof_pos[(dma_it+1)*test_pkg::REGIONS*$clog2(test_pkg::MFB_REG_SIZE) -1 -: test_pkg::REGIONS*$clog2(test_pkg::MFB_REG_SIZE)]                                                   = dma_rx_mfb[dma_it].SOF_POS;
        assign dma_rx_mfb_eof_pos[(dma_it+1)*test_pkg::REGIONS*$clog2(test_pkg::MFB_REG_SIZE*test_pkg::MFB_BLOCK_SIZE) -1 -: test_pkg::REGIONS*$clog2(test_pkg::MFB_REG_SIZE*test_pkg::MFB_BLOCK_SIZE)] = dma_rx_mfb[dma_it].EOF_POS;
        assign dma_rx_mfb_src_rdy[dma_it] = dma_rx_mfb[dma_it].SRC_RDY;
        assign dma_rx_mfb[dma_it].DST_RDY = dma_rx_mfb_dst_rdy[dma_it];

        //DMA TX
        for (genvar dma_region = 0; dma_region < test_pkg::REGIONS; dma_region++) begin
            assign dma_tx_mvb[dma_it].DATA[dma_region*DMA_TX_MVB_WIDTH + $clog2(test_pkg::DMA_PKT_MTU+1)-1 -: $clog2(test_pkg::DMA_PKT_MTU+1)]                                                                  = dma_tx_mvb_len[(dma_it*test_pkg::REGIONS + dma_region + 1) * $clog2(test_pkg::DMA_PKT_MTU+1)-1 -: $clog2(test_pkg::DMA_PKT_MTU+1)];
            assign dma_tx_mvb[dma_it].DATA[dma_region*DMA_TX_MVB_WIDTH + $clog2(test_pkg::DMA_PKT_MTU+1)+test_pkg::DMA_HDR_META_WIDTH-1 -: test_pkg::DMA_HDR_META_WIDTH]                                        = dma_tx_mvb_hdr_meta[(dma_it*test_pkg::REGIONS + dma_region + 1) * test_pkg::DMA_HDR_META_WIDTH-1 -: test_pkg::DMA_HDR_META_WIDTH];
            assign dma_tx_mvb[dma_it].DATA[dma_region*DMA_TX_MVB_WIDTH + $clog2(test_pkg::DMA_PKT_MTU+1)+test_pkg::DMA_HDR_META_WIDTH+$clog2(test_pkg::DMA_RX_CHANNELS)-1 -: $clog2(test_pkg::DMA_RX_CHANNELS)] = dma_tx_mvb_channel[(dma_it*test_pkg::REGIONS + dma_region + 1) *  $clog2(test_pkg::DMA_RX_CHANNELS)-1 -: $clog2(test_pkg::DMA_RX_CHANNELS)];
            assign dma_tx_mvb[dma_it].DATA[dma_region*DMA_TX_MVB_WIDTH + $clog2(test_pkg::DMA_PKT_MTU+1)+test_pkg::DMA_HDR_META_WIDTH+$clog2(test_pkg::DMA_RX_CHANNELS)+1-1 -: 1]                               = dma_tx_mvb_discard[dma_it*test_pkg::REGIONS + dma_region];
            assign dma_tx_mvb[dma_it].VLD[dma_region] = dma_tx_mvb_vld[dma_it*test_pkg::REGIONS + dma_region];
        end
        assign dma_tx_mvb[dma_it].SRC_RDY = dma_tx_mvb_src_rdy[dma_it];
        assign dma_tx_mvb_dst_rdy[dma_it] = dma_tx_mvb[dma_it].DST_RDY;

        assign dma_tx_mfb[dma_it].DATA    = dma_tx_mfb_data[(dma_it+1)*test_pkg::REGIONS*test_pkg::MFB_REG_SIZE*test_pkg::MFB_BLOCK_SIZE*test_pkg::MFB_ITEM_WIDTH -1 -: test_pkg::REGIONS*test_pkg::MFB_REG_SIZE*test_pkg::MFB_BLOCK_SIZE*test_pkg::MFB_ITEM_WIDTH];
        assign dma_tx_mfb[dma_it].SOF     = dma_tx_mfb_sof[(dma_it+1)*test_pkg::REGIONS -1 -: test_pkg::REGIONS];
        assign dma_tx_mfb[dma_it].EOF     = dma_tx_mfb_eof[(dma_it+1)*test_pkg::REGIONS -1 -: test_pkg::REGIONS];
        assign dma_tx_mfb[dma_it].SOF_POS = dma_tx_mfb_sof_pos[(dma_it+1)*test_pkg::REGIONS*$clog2(test_pkg::MFB_REG_SIZE) -1 -: test_pkg::REGIONS*$clog2(test_pkg::MFB_REG_SIZE)];
        assign dma_tx_mfb[dma_it].EOF_POS = dma_tx_mfb_eof_pos[(dma_it+1)*test_pkg::REGIONS*$clog2(test_pkg::MFB_REG_SIZE*test_pkg::MFB_BLOCK_SIZE) -1 -: test_pkg::REGIONS*$clog2(test_pkg::MFB_REG_SIZE*test_pkg::MFB_BLOCK_SIZE)];
        assign dma_tx_mfb[dma_it].SRC_RDY = dma_tx_mfb_src_rdy[dma_it];
        assign dma_tx_mfb_dst_rdy[dma_it] = dma_tx_mfb[dma_it].DST_RDY;
    end


    APPLICATION_CORE  #(
        .ETH_PORTS         (test_pkg::ETH_PORTS),
        .ETH_CHANNELS      (test_pkg::ETH_CHANNELS),
        .ETH_STREAMS       (test_pkg::ETH_STREAMS),
        .ETH_PKT_MTU       (test_pkg::ETH_PKT_MTU),
        .PCIE_ENDPOINTS    (test_pkg::PCIE_ENDPOINTS),
        .DMA_STREAMS       (test_pkg::DMA_STREAMS),
        .DMA_RX_CHANNELS   (test_pkg::DMA_RX_CHANNELS),
        .DMA_TX_CHANNELS   (test_pkg::DMA_TX_CHANNELS),
        .DMA_HDR_META_WIDTH(test_pkg::DMA_HDR_META_WIDTH),
        .DMA_PKT_MTU       (test_pkg::DMA_PKT_MTU),
        .MFB_REGIONS       (test_pkg::REGIONS),
        .MFB_REG_SIZE      (test_pkg::MFB_REG_SIZE),
        .MFB_BLOCK_SIZE    (test_pkg::MFB_BLOCK_SIZE),
        .MFB_ITEM_WIDTH    (test_pkg::MFB_ITEM_WIDTH),
        .MEM_PORTS         (test_pkg::MEM_PORTS),
        .MEM_ADDR_WIDTH    (test_pkg::MEM_ADDR_WIDTH),
        .MEM_BURST_WIDTH   (test_pkg::MEM_BURST_WIDTH),
        .MEM_DATA_WIDTH    (test_pkg::MEM_DATA_WIDTH),
        .MI_DATA_WIDTH     (test_pkg::MI_DATA_WIDTH),
        .MI_ADDR_WIDTH     (test_pkg::MI_ADDR_WIDTH),
        .RESET_WIDTH       (test_pkg::RESET_WIDTH),
        .BOARD             (test_pkg::BOARD),
        .DEVICE            (test_pkg::DEVICE)
    )
    DUT (
        .CLK_USER              (CLK_USER_X1), //  : in  std_logic;
        .CLK_USER_X2           (CLK_USER_X2), //  : in  std_logic;
        .CLK_USER_X3           (CLK_USER_X3), //  : in  std_logic;
        .CLK_USER_X4           (CLK_USER_X4), //  : in  std_logic;

        .RESET_USER            (reset_logic_user_x1), //  : in  std_logic_vector(RESET_WIDTH-1 downto 0);
        .RESET_USER_X2         (reset_logic_user_x2), //  : in  std_logic_vector(RESET_WIDTH-1 downto 0);
        .RESET_USER_X3         (reset_logic_user_x3), //  : in  std_logic_vector(RESET_WIDTH-1 downto 0);
        .RESET_USER_X4         (reset_logic_user_x4), //  : in  std_logic_vector(RESET_WIDTH-1 downto 0);

        .MI_CLK                (MI_CLK),     //  : out std_logic;
        .DMA_CLK               (DMA_CLK_X1), //  : out std_logic;
        .DMA_CLK_X2            (DMA_CLK_X2), //  : out std_logic;
        .APP_CLK               (APP_CLK),    //  : out std_logic;

        .MI_RESET              (reset_logic_mi),     //  : out std_logic_vector(RESET_WIDTH-1 downto 0);
        .DMA_RESET             (reset_logic_dma_x1), //  : out std_logic_vector(RESET_WIDTH-1 downto 0);
        .DMA_RESET_X2          (reset_logic_dma_x2), //  : out std_logic_vector(RESET_WIDTH-1 downto 0);
        .APP_RESET             (reset_logic_app),    //  : out std_logic_vector(RESET_WIDTH-1 downto 0);

        .PCIE_LINK_UP          (), //  : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        .ETH_RX_LINK_UP        (), //  : in  std_logic_vector(ETH_STREAMS*ETH_CHANNELS-1 downto 0);

        .ETH_RX_MVB_DATA       (eth_rx_mvb_data),    //  : in  std_logic_vector(ETH_STREAMS*MFB_REGIONS*ETH_RX_HDR_WIDTH-1 downto 0);
        .ETH_RX_MVB_VLD        (eth_rx_mvb_vld),     //  : in  std_logic_vector(ETH_STREAMS*MFB_REGIONS-1 downto 0);
        .ETH_RX_MVB_SRC_RDY    (eth_rx_mvb_src_rdy), //  : in  std_logic_vector(ETH_STREAMS-1 downto 0);
        .ETH_RX_MVB_DST_RDY    (eth_rx_mvb_dst_rdy), //  : out std_logic_vector(ETH_STREAMS-1 downto 0);

        .ETH_RX_MFB_DATA       (eth_rx_mfb_data),    //  : in  std_logic_vector(ETH_STREAMS*MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        .ETH_RX_MFB_SOF        (eth_rx_mfb_sof),     //  : in  std_logic_vector(ETH_STREAMS*MFB_REGIONS-1 downto 0);
        .ETH_RX_MFB_EOF        (eth_rx_mfb_eof),     //  : in  std_logic_vector(ETH_STREAMS*MFB_REGIONS-1 downto 0);
        .ETH_RX_MFB_SOF_POS    (eth_rx_mfb_sof_pos), //  : in  std_logic_vector(ETH_STREAMS*MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
        .ETH_RX_MFB_EOF_POS    (eth_rx_mfb_eof_pos), //  : in  std_logic_vector(ETH_STREAMS*MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        .ETH_RX_MFB_SRC_RDY    (eth_rx_mfb_src_rdy), //  : in  std_logic_vector(ETH_STREAMS-1 downto 0);
        .ETH_RX_MFB_DST_RDY    (eth_rx_mfb_dst_rdy), //  : out std_logic_vector(ETH_STREAMS-1 downto 0);

        .ETH_TX_MFB_DATA       (eth_tx_mfb_data),    //  : out std_logic_vector(ETH_STREAMS*MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        .ETH_TX_MFB_HDR        (eth_tx_mfb_meta),    //  : out std_logic_vector(ETH_STREAMS*MFB_REGIONS*ETH_TX_HDR_WIDTH-1 downto 0) := (others => '0');
        .ETH_TX_MFB_SOF        (eth_tx_mfb_sof),     //  : out std_logic_vector(ETH_STREAMS*MFB_REGIONS-1 downto 0);
        .ETH_TX_MFB_EOF        (eth_tx_mfb_eof),     //  : out std_logic_vector(ETH_STREAMS*MFB_REGIONS-1 downto 0);
        .ETH_TX_MFB_SOF_POS    (eth_tx_mfb_sof_pos), //  : out std_logic_vector(ETH_STREAMS*MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
        .ETH_TX_MFB_EOF_POS    (eth_tx_mfb_eof_pos), //  : out std_logic_vector(ETH_STREAMS*MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        .ETH_TX_MFB_SRC_RDY    (eth_tx_mfb_src_rdy), //  : out std_logic_vector(ETH_STREAMS-1 downto 0);
        .ETH_TX_MFB_DST_RDY    (eth_tx_mfb_dst_rdy), //  : in  std_logic_vector(ETH_STREAMS-1 downto 0);

        .DMA_RX_MVB_LEN        (dma_tx_mvb_len),      //   : out std_logic_vector(DMA_STREAMS*MFB_REGIONS*log2(DMA_PKT_MTU+1)-1 downto 0);
        .DMA_RX_MVB_HDR_META   (dma_tx_mvb_hdr_meta), //   : out std_logic_vector(DMA_STREAMS*MFB_REGIONS*DMA_HDR_META_WIDTH-1 downto 0);
        .DMA_RX_MVB_CHANNEL    (dma_tx_mvb_channel),  //   : out std_logic_vector(DMA_STREAMS*MFB_REGIONS*log2(DMA_RX_CHANNELS)-1 downto 0);
        .DMA_RX_MVB_DISCARD    (dma_tx_mvb_discard),  //   : out std_logic_vector(DMA_STREAMS*MFB_REGIONS-1 downto 0);
        .DMA_RX_MVB_VLD        (dma_tx_mvb_vld),      //   : out std_logic_vector(DMA_STREAMS*MFB_REGIONS-1 downto 0);
        .DMA_RX_MVB_SRC_RDY    (dma_tx_mvb_src_rdy),  //   : out std_logic_vector(DMA_STREAMS-1 downto 0);
        .DMA_RX_MVB_DST_RDY    (dma_tx_mvb_dst_rdy),  //   : in  std_logic_vector(DMA_STREAMS-1 downto 0);

        .DMA_RX_MFB_DATA       (dma_tx_mfb_data),    //   : out std_logic_vector(DMA_STREAMS*MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        .DMA_RX_MFB_SOF        (dma_tx_mfb_sof),     //   : out std_logic_vector(DMA_STREAMS*MFB_REGIONS-1 downto 0);
        .DMA_RX_MFB_EOF        (dma_tx_mfb_eof),     //   : out std_logic_vector(DMA_STREAMS*MFB_REGIONS-1 downto 0);
        .DMA_RX_MFB_SOF_POS    (dma_tx_mfb_sof_pos), //   : out std_logic_vector(DMA_STREAMS*MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
        .DMA_RX_MFB_EOF_POS    (dma_tx_mfb_eof_pos), //   : out std_logic_vector(DMA_STREAMS*MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        .DMA_RX_MFB_SRC_RDY    (dma_tx_mfb_src_rdy), //   : out std_logic_vector(DMA_STREAMS-1 downto 0);
        .DMA_RX_MFB_DST_RDY    (dma_tx_mfb_dst_rdy), //   : in  std_logic_vector(DMA_STREAMS-1 downto 0);

        .DMA_TX_MVB_LEN        (dma_rx_mvb_len),     //  : in  std_logic_vector(DMA_STREAMS*MFB_REGIONS*log2(DMA_PKT_MTU+1)-1 downto 0);
        .DMA_TX_MVB_HDR_META   (dma_rx_mvb_hdr_meta),//  : in  std_logic_vector(DMA_STREAMS*MFB_REGIONS*DMA_HDR_META_WIDTH-1 downto 0);
        .DMA_TX_MVB_CHANNEL    (dma_rx_mvb_channel), //  : in  std_logic_vector(DMA_STREAMS*MFB_REGIONS*log2(DMA_TX_CHANNELS)-1 downto 0);
        .DMA_TX_MVB_VLD        (dma_rx_mvb_vld),     //  : in  std_logic_vector(DMA_STREAMS*MFB_REGIONS-1 downto 0);
        .DMA_TX_MVB_SRC_RDY    (dma_rx_mvb_src_rdy), //  : in  std_logic_vector(DMA_STREAMS-1 downto 0);
        .DMA_TX_MVB_DST_RDY    (dma_rx_mvb_dst_rdy), //  : out std_logic_vector(DMA_STREAMS-1 downto 0);

        .DMA_TX_MFB_DATA       (dma_rx_mfb_data),    //  : in  std_logic_vector(DMA_STREAMS*MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        .DMA_TX_MFB_SOF        (dma_rx_mfb_sof),     //  : in  std_logic_vector(DMA_STREAMS*MFB_REGIONS-1 downto 0);
        .DMA_TX_MFB_EOF        (dma_rx_mfb_eof),     //  : in  std_logic_vector(DMA_STREAMS*MFB_REGIONS-1 downto 0);
        .DMA_TX_MFB_SOF_POS    (dma_rx_mfb_sof_pos), //  : in  std_logic_vector(DMA_STREAMS*MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
        .DMA_TX_MFB_EOF_POS    (dma_rx_mfb_eof_pos), //  : in  std_logic_vector(DMA_STREAMS*MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        .DMA_TX_MFB_SRC_RDY    (dma_rx_mfb_src_rdy), //  : in  std_logic_vector(DMA_STREAMS-1 downto 0);
        .DMA_TX_MFB_DST_RDY    (dma_rx_mfb_dst_rdy), //  : out std_logic_vector(DMA_STREAMS-1 downto 0);

        .MEM_CLK               (clk_logic_mem),   // : in  std_logic_vector(MEM_PORTS-1 downto 0);
        .MEM_RST               (reset_logic_mem), // : in  std_logic_vector(MEM_PORTS-1 downto 0);

        .MEM_AVMM_READY        (), // : in  std_logic_vector(MEM_PORTS-1 downto 0);
        .MEM_AVMM_READ         (), // : out std_logic_vector(MEM_PORTS-1 downto 0);
        .MEM_AVMM_WRITE        (), // : out std_logic_vector(MEM_PORTS-1 downto 0);
        .MEM_AVMM_ADDRESS      (), // : out std_logic_vector(MEM_PORTS*MEM_ADDR_WIDTH-1 downto 0);
        .MEM_AVMM_BURSTCOUNT   (), // : out std_logic_vector(MEM_PORTS*MEM_BURST_WIDTH-1 downto 0);
        .MEM_AVMM_WRITEDATA    (), // : out std_logic_vector(MEM_PORTS*MEM_DATA_WIDTH-1 downto 0);
        .MEM_AVMM_READDATA     (), // : in  std_logic_vector(MEM_PORTS*MEM_DATA_WIDTH-1 downto 0);
        .MEM_AVMM_READDATAVALID(), // : in  std_logic_vector(MEM_PORTS-1 downto 0);

        .EMIF_RST_REQ          (), // : out std_logic_vector(MEM_PORTS-1 downto 0);
        .EMIF_RST_DONE         (), // : in  std_logic_vector(MEM_PORTS-1 downto 0);
        .EMIF_ECC_USR_INT      (), // : in  std_logic_vector(MEM_PORTS-1 downto 0);
        .EMIF_CAL_SUCCESS      (), // : in  std_logic_vector(MEM_PORTS-1 downto 0);
        .EMIF_CAL_FAIL         (), // : in  std_logic_vector(MEM_PORTS-1 downto 0);

        .MI_DWR                (config_if.DWR),  //  : in  std_logic_vector(MI_DATA_WIDTH-1 downto 0);
        .MI_ADDR               (config_if.ADDR), //  : in  std_logic_vector(MI_ADDR_WIDTH-1 downto 0);
        .MI_BE                 (config_if.BE),   //  : in  std_logic_vector(MI_DATA_WIDTH/8-1 downto 0);
        .MI_RD                 (config_if.RD),   //  : in  std_logic;
        .MI_WR                 (config_if.WR),   //  : in  std_logic;
        .MI_ARDY               (config_if.ARDY), //  : out std_logic;
        .MI_DRD                (config_if.DRD),  //  : out std_logic_vector(MI_DATA_WIDTH-1 downto 0);
        .MI_DRDY               (config_if.DRDY)  //  : out std_logic
    );


    app_core_property #(
        .ETH_STREAMS (test_pkg::ETH_STREAMS),
        .DMA_STREAMS (test_pkg::DMA_STREAMS),
        .REGIONS     (test_pkg::REGIONS),
        .MFB_REGION_SIZE (test_pkg::MFB_REG_SIZE),
        .MFB_BLOCK_SIZE  (test_pkg::MFB_BLOCK_SIZE),
        .MFB_ITEM_WIDTH  (test_pkg::MFB_ITEM_WIDTH),

        .CHECK_RX  (1'b1)
    )
    property_assertion(
       .RESET (reset_app.RESET),
       .eth_tx_mfb (eth_tx_mfb),
       //.eth_tx_mvb (eth_tx_mvb),
       .dma_tx_mfb (dma_tx_mfb),
       .dma_tx_mvb (dma_tx_mvb),

        .eth_rx_mfb (eth_rx_mfb),
        .eth_rx_mvb (eth_rx_mvb),
        .dma_rx_mfb (dma_rx_mfb),
        .dma_rx_mvb (dma_rx_mvb)
    );


    initial begin
        uvm_root m_root;
        // CONNECT INTERFACES
        automatic virtual mvb_if #(test_pkg::REGIONS, test_pkg::ETH_RX_HDR_WIDTH)                                                    vir_eth_rx_mvb[test_pkg::ETH_STREAMS] = eth_rx_mvb;
        automatic virtual mfb_if #(test_pkg::REGIONS, test_pkg::MFB_REG_SIZE, test_pkg::MFB_BLOCK_SIZE, test_pkg::MFB_ITEM_WIDTH, 0) vir_eth_rx_mfb[test_pkg::ETH_STREAMS] = eth_rx_mfb;
        automatic virtual mfb_if #(test_pkg::REGIONS, test_pkg::MFB_REG_SIZE, test_pkg::MFB_BLOCK_SIZE, test_pkg::MFB_ITEM_WIDTH, test_pkg::ETH_TX_HDR_WIDTH) vir_eth_tx_mfb[test_pkg::ETH_STREAMS] = eth_tx_mfb;
        // DMA I/O INTERFACE
        automatic virtual mvb_if #(test_pkg::REGIONS, DMA_TX_MVB_WIDTH)                                                              vir_dma_tx_mvb[test_pkg::DMA_STREAMS] = dma_tx_mvb;
        automatic virtual mfb_if #(test_pkg::REGIONS, test_pkg::MFB_REG_SIZE, test_pkg::MFB_BLOCK_SIZE, test_pkg::MFB_ITEM_WIDTH, 0) vir_dma_tx_mfb[test_pkg::DMA_STREAMS] = dma_tx_mfb;
        automatic virtual mvb_if #(test_pkg::REGIONS, DMA_RX_MVB_WIDTH)                                                              vir_dma_rx_mvb[test_pkg::DMA_STREAMS] = dma_rx_mvb;
        automatic virtual mfb_if #(test_pkg::REGIONS, test_pkg::MFB_REG_SIZE, test_pkg::MFB_BLOCK_SIZE, test_pkg::MFB_ITEM_WIDTH, 0) vir_dma_rx_mfb[test_pkg::DMA_STREAMS] = dma_rx_mfb;
        //RESET
        automatic virtual reset_if vir_reset_mem[test_pkg::MEM_PORTS] = reset_mem;


        /////////////////////////////////////////////
        //SAVE ETH interface to configuration database
        for (int unsigned it = 0; it < test_pkg::ETH_STREAMS; it++) begin
            string it_num;
            it_num.itoa(it);

            uvm_config_db#(virtual mvb_if #(test_pkg::REGIONS, test_pkg::ETH_RX_HDR_WIDTH)                                          )::set(null, "", {"ETH_RX_MVB_", it_num}, vir_eth_rx_mvb[it]);
            uvm_config_db#(virtual mfb_if #(test_pkg::REGIONS, test_pkg::MFB_REG_SIZE, test_pkg::MFB_BLOCK_SIZE, test_pkg::MFB_ITEM_WIDTH, 0))::set(null, "", {"ETH_RX_MFB_", it_num}, vir_eth_rx_mfb[it]);
            uvm_config_db#(virtual mfb_if #(test_pkg::REGIONS, test_pkg::MFB_REG_SIZE, test_pkg::MFB_BLOCK_SIZE, test_pkg::MFB_ITEM_WIDTH, test_pkg::ETH_TX_HDR_WIDTH))::set(null, "", {"ETH_TX_MFB_", it_num}, vir_eth_tx_mfb[it]);
        end
        //SAVE DMA interface to configuration database
        for (int unsigned it = 0; it < test_pkg::DMA_STREAMS; it++) begin
            string it_num;
            it_num.itoa(it);

            uvm_config_db#(virtual mvb_if #(test_pkg::REGIONS,   DMA_TX_MVB_WIDTH)                                                        )::set(null, "", {"DMA_TX_MVB_", it_num}, vir_dma_tx_mvb[it]);
            uvm_config_db#(virtual mfb_if #(test_pkg::REGIONS, test_pkg::MFB_REG_SIZE, test_pkg::MFB_BLOCK_SIZE, test_pkg::MFB_ITEM_WIDTH, 0))::set(null, "", {"DMA_TX_MFB_", it_num}, vir_dma_tx_mfb[it]);
            uvm_config_db#(virtual mvb_if #(test_pkg::REGIONS,   DMA_RX_MVB_WIDTH)                                                        )::set(null, "", {"DMA_RX_MVB_", it_num}, vir_dma_rx_mvb[it]);
            uvm_config_db#(virtual mfb_if #(test_pkg::REGIONS, test_pkg::MFB_REG_SIZE, test_pkg::MFB_BLOCK_SIZE, test_pkg::MFB_ITEM_WIDTH, 0))::set(null, "", {"DMA_RX_MFB_", it_num}, vir_dma_rx_mfb[it]);
        end

        //SAVE RESETS interface to configuration database
        uvm_config_db#(virtual reset_if)::set(null, "", "RESET_USER_X1", reset_user_x1);
        uvm_config_db#(virtual reset_if)::set(null, "", "RESET_USER_X2", reset_user_x2);
        uvm_config_db#(virtual reset_if)::set(null, "", "RESET_USER_X3", reset_user_x3);
        uvm_config_db#(virtual reset_if)::set(null, "", "RESET_USER_X4", reset_user_x4);
        uvm_config_db#(virtual reset_if)::set(null, "", "RESET_MI",      reset_mi);
        uvm_config_db#(virtual reset_if)::set(null, "", "RESET_DMA_X1",  reset_dma_x1);
        uvm_config_db#(virtual reset_if)::set(null, "", "RESET_DMA_X2",  reset_dma_x2);
        uvm_config_db#(virtual reset_if)::set(null, "", "RESET_APP",     reset_app);
        for (int unsigned it = 0; it < test_pkg::MEM_PORTS; it++) begin
            string it_num;
            it_num.itoa(it);

            uvm_config_db#(virtual reset_if)::set(null, "", {"RESET_MEM_", it_num}, vir_reset_mem[it]);
        end

        //CONFIGURE INF
        uvm_config_db#(virtual mi_if#(test_pkg::MI_DATA_WIDTH, test_pkg::MI_ADDR_WIDTH))::set(null, "", "MI_INTERFACE", config_if);

        /////////////////////////////////////////////
        // RUN TEST
        m_root = uvm_root::get();
        m_root.finish_on_completion = 0;
        m_root.set_report_id_action_hier("ILLEGALNAME",UVM_NO_ACTION);

        run_test();

        $stop(2);
    end
endmodule
