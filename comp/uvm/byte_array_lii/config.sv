/*
 * file       : config.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: Configuration file for byte_array to lii enviroment
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef RX_ENV_CONFIG_SV
`define RX_ENV_CONFIG_SV

class config_item extends uvm_object;

    typedef enum {PCS, RX_MAC, TX_MAC, ETH_PHY} sequence_type;
    ////////////////
    // configuration variables
    uvm_active_passive_enum active;
    string interface_name;
    sequence_type type_of_sequence;

    ////////////////
    // functions
    function new (string name = "");
        super.new(name);
    endfunction
endclass

`endif
