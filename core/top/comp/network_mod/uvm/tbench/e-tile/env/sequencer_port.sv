// sequencer_port.sv: Virtual sequencer port
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class sequencer_port #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, int unsigned ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH) extends uvm_network_mod_env::sequencer_port #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH);
    `uvm_component_param_utils(uvm_network_mod_e_tile_env::sequencer_port #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH))

    uvm_logic_vector_array::sequencer#(ITEM_WIDTH)  eth_rx_data;
    uvm_logic_vector::sequencer#(6)                 eth_rx_meta;
    uvm_avst::sequencer #(ETH_PORT_CHAN, 1, REGION_SIZE * BLOCK_SIZE, ITEM_WIDTH, 1) eth_tx;

    function new(string name = "sequencer_port", uvm_component parent = null);
        super.new(name, parent);
    endfunction

endclass
