/*
 * file       :  sequencer.sv
 * Copyright (C) 2024 CESNET z. s. p. o.
 * description: verification top sequencer 
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/



class sequencer#(
    int unsigned DMA_TX_CHANNELS,
    int unsigned DMA_RX_CHANNELS,
    int unsigned DMA_PKT_MTU,
    int unsigned DMA_HDR_META_WIDTH,
    int unsigned DMA_STREAMS,
    int unsigned ETH_TX_HDR_WIDTH,
    int unsigned MFB_ITEM_WIDTH,
    int unsigned ETH_STREAMS,
    int unsigned REGIONS,
    int unsigned MFB_REG_SIZE,
    int unsigned MFB_BLOCK_SIZE,
    int unsigned MEM_PORTS,
    int unsigned MEM_ADDR_WIDTH,
    int unsigned MEM_DATA_WIDTH,
    int unsigned MEM_BURST_WIDTH
) extends uvm_sequencer;
    `uvm_component_param_utils(uvm_app_core::sequencer#(DMA_TX_CHANNELS, DMA_RX_CHANNELS, DMA_PKT_MTU, DMA_HDR_META_WIDTH, DMA_STREAMS, ETH_TX_HDR_WIDTH,
                                MFB_ITEM_WIDTH, ETH_STREAMS, REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MEM_PORTS, MEM_ADDR_WIDTH, MEM_DATA_WIDTH, MEM_BURST_WIDTH))

    localparam DMA_RX_MVB_WIDTH = $clog2(DMA_PKT_MTU+1)+DMA_HDR_META_WIDTH+$clog2(DMA_RX_CHANNELS);
    localparam DMA_TX_MVB_WIDTH = $clog2(DMA_PKT_MTU+1)+DMA_HDR_META_WIDTH+$clog2(DMA_TX_CHANNELS) + 1;

    // CHANNEL_WIDTH + LENGHT_WIDTH + FLAGS  +  MAC_HIT  + TSU WIDTH
    localparam ETH_RX_META_WIDTH   = 8 + 16 + 10 + 4 + 64;

    //ETH
    uvm_app_core_top_agent::sequencer #(MFB_ITEM_WIDTH, ETH_RX_META_WIDTH)                       m_eth_rx[ETH_STREAMS];
    uvm_mfb::sequencer#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, ETH_TX_HDR_WIDTH) m_eth_tx[ETH_STREAMS];

    //DMA
    uvm_app_core_top_agent::sequencer#(MFB_ITEM_WIDTH, DMA_RX_MVB_WIDTH)            m_dma_rx[DMA_STREAMS];
    uvm_mvb::sequencer#(REGIONS, DMA_TX_MVB_WIDTH)                                  m_dma_mvb_tx[DMA_STREAMS];
    uvm_mfb::sequencer#(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0)   m_dma_mfb_tx[DMA_STREAMS];

    //RESET
    uvm_reset::sequencer m_resets_gen;
    uvm_reset::sequencer m_resets_mi;
    uvm_reset::sequencer m_resets_dma;
    uvm_reset::sequencer m_resets_app;
    uvm_reset::sequencer m_resets_mem;

    //External memory
    uvm_avmm::sequencer_master#(MEM_ADDR_WIDTH, MEM_DATA_WIDTH, MEM_BURST_WIDTH) m_memory[MEM_PORTS];

    //CONFIGURATION INTERFACE
    uvm_app_core::regmodel m_regmodel;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

endclass


