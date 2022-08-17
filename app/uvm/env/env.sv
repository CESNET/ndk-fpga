/*
 * file       : env.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: verification eviroment for application core
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


class env #(ETH_STREAMS, ETH_CHANNELS, ETH_PKT_MTU, ETH_RX_HDR_WIDTH, ETH_TX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU, REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MEM_PORTS, MEM_ADDR_WIDTH, MEM_BURST_WIDTH, MEM_DATA_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH)
            extends uvm_app_core::env#(ETH_STREAMS, ETH_CHANNELS, ETH_PKT_MTU, ETH_RX_HDR_WIDTH, ETH_TX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU, REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MEM_PORTS, MEM_ADDR_WIDTH, MEM_BURST_WIDTH, MEM_DATA_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH);
    `uvm_component_param_utils(uvm_app_core_minimal::env#(ETH_STREAMS, ETH_CHANNELS, ETH_PKT_MTU, ETH_RX_HDR_WIDTH, ETH_TX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU,
            REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MEM_PORTS, MEM_ADDR_WIDTH, MEM_BURST_WIDTH, MEM_DATA_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH))

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);

        uvm_app_core::regmodel#(ETH_STREAMS, ETH_CHANNELS, DMA_RX_CHANNELS)::type_id::set_inst_override(regmodel#(ETH_STREAMS, ETH_CHANNELS, DMA_RX_CHANNELS)::get_type(), {this.get_full_name() ,".m_regmodel.*"});

        uvm_app_core::model#(ETH_STREAMS, ETH_CHANNELS, ETH_RX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU, REGIONS, MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::set_inst_override(
        model#(ETH_STREAMS, ETH_CHANNELS, ETH_RX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU, REGIONS, MI_DATA_WIDTH, MI_ADDR_WIDTH)::get_type(), {this.get_full_name() ,".m_scoreboard.m_model"});
        //mfb_rx::transaction #(ITEM_WIDTH, MFB_META_RX_WIDTH)::type_id::set_inst_override(mfb_transaction::get_type(), {this.get_full_name() ,".m_mfb_rx_agent_ptc.*"})

        super.build_phase(phase);
        //m_env =  uvm_app_core::env#(ETH_STREAMS, ETH_CHANNELS, ETH_PKT_MTU, ETH_RX_HDR_WIDTH, ETH_TX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU,
        //    REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MEM_PORTS, MEM_ADDR_WIDTH, MEM_BURST_WIDTH, MEM_DATA_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::create("m_env", this);
    endfunction
endclass

