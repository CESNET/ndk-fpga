// model.sv: Model for Intel F-Tile device
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class model #(string ETH_CORE_ARCH, int unsigned ETH_PORTS, int unsigned ETH_PORT_SPEED[ETH_PORTS-1:0], int unsigned ETH_PORT_CHAN[ETH_PORTS-1:0], REGIONS, ITEM_WIDTH, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH) extends uvm_network_mod_env::model #(ETH_CORE_ARCH, ETH_PORTS, ETH_PORT_SPEED, ETH_PORT_CHAN, REGIONS, ITEM_WIDTH, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH);
    `uvm_component_param_utils(uvm_network_mod_f_tile_env::model #(ETH_CORE_ARCH, ETH_PORTS, ETH_PORT_SPEED, ETH_PORT_CHAN, REGIONS, ITEM_WIDTH, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH));

    // Constructor
    function new(string name = "model", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function logic is_frame_valid(logic [6-1 : 0] error_data);
        logic           fcs_error;
        logic [2-1 : 0] error;
        logic [3-1 : 0] status_data;

        { fcs_error, error, status_data } = error_data;

        return !fcs_error;
    endfunction

endclass
