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
) extends uvm_network_mod_env::sequencer_port #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE,
                                                BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH);
    `uvm_component_param_utils(uvm_network_mod_cmac_env::sequencer_port #(
        ETH_TX_HDR_WIDTH,
        ETH_RX_HDR_WIDTH,
        ITEM_WIDTH,
        REGIONS,
        REGION_SIZE,
        BLOCK_SIZE,
        ETH_PORT_CHAN,
        MI_DATA_WIDTH,
        MI_ADDR_WIDTH
    ))

    uvm_logic_vector_array::sequencer #(8) eth_rx_packet;
    uvm_logic_vector::sequencer       #(1) eth_rx_error;
    uvm_lbus::sequencer                    eth_tx;

    // Constructor
    function new(string name = "sequencer_port", uvm_component parent = null);
        super.new(name, parent);
    endfunction

endclass
