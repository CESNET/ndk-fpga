// sequence_frame_length_configuration.sv: Configuration sequence for the frame lengths in RX MAC Lite
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

// TODO: Multi-channel support

class sequence_frame_length_configuration #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH) extends uvm_sequence;
    `uvm_object_param_utils(uvm_network_mod_env::sequence_frame_length_configuration #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH))
    `uvm_declare_p_sequencer(uvm_network_mod_env::sequencer_port #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH))

    int unsigned minimum_length_max = 256;
    int unsigned minimum_length_min = 60;

    rand int unsigned minimum_length;
    constraint c_minimum_length {
        minimum_length_min <= minimum_length;
        minimum_length <= minimum_length_max;
    }

    int unsigned maximum_length_max = 16384;
    int unsigned maximum_length_min = 1500;

    rand int unsigned maximum_length;
    constraint c_maximum_length {
        maximum_length_min <= maximum_length;
        maximum_length <= maximum_length_max;
    }

    // Constructor
    function new(string name = "sequence_frame_length_configuration");
        super.new(name);
    endfunction

    task body;
        configure_minimum_length();
        configure_maximum_length();
    endtask

    protected virtual task configure_minimum_length();
        uvm_status_e status;
        p_sequencer.regmodel.channel[0].rx_mac.min.write(status, minimum_length);
    endtask

    protected virtual task configure_maximum_length();
        uvm_status_e status;
        p_sequencer.regmodel.channel[0].rx_mac.max.write(status, maximum_length);
    endtask

endclass
