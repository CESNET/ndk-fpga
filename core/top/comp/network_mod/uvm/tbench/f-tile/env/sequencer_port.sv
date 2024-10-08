// sequencer_port.sv: Virtual sequencer port
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class sequencer_port #(
    int unsigned ETH_TX_HDR_WIDTH,
    int unsigned ETH_RX_HDR_WIDTH,
    
    int unsigned ITEM_WIDTH,
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned BLOCK_SIZE,
    
    int unsigned ETH_PORT_CHAN,
    
    int unsigned MI_DATA_WIDTH,
    int unsigned MI_ADDR_WIDTH
) extends uvm_network_mod_env::sequencer_port #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH);
    `uvm_component_param_utils(uvm_network_mod_f_tile_env::sequencer_port #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH))

    localparam int unsigned ERROR_WIDTH = 6;

    uvm_logic_vector_array::sequencer #(ITEM_WIDTH)  eth_rx_data;
    uvm_logic_vector::sequencer       #(ERROR_WIDTH) eth_rx_meta;
    uvm_intel_mac_seg::sequencer      #(SEGMENTS)    eth_tx;

    function new(string name = "sequencer_port", uvm_component parent = null);
        super.new(name, parent);
    endfunction

endclass
