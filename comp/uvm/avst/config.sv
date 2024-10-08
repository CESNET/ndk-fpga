//-- config.sv: Configuration object for AVST env
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause
`ifndef AVST_CONFIG_SV
`define AVST_CONFIG_SV

class config_sequence extends uvm_object;
    `uvm_object_utils(uvm_avst::config_sequence)

    uvm_common::sequence_cfg state;

    // configuration of probability of rdy signal in percentige
    int unsigned rdy_probability_min = 0;   // inside [0:100]
    int unsigned rdy_probability_max = 100; // inside [0:100]

    function new(string name = "uvm_logic_vector_array_mfb::config_sequence");
        super.new(name);
        state = null;
    endfunction

    function void probability_set(int unsigned min, int unsigned max);
        rdy_probability_min = min;
        rdy_probability_max = max;
    endfunction
endclass


class config_item extends uvm_object;

    // ------------------------------------------------------------------------
    // Configuration variables
    uvm_active_passive_enum active;
    string interface_name;

    // ------------------------------------------------------------------------
    // Constructor
    function new (string name = "");
        super.new(name);
    endfunction

endclass

`endif
