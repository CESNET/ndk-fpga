//-- config.sv:
//-- Copyright (C) 2026 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class config_sequence extends uvm_object;
    `uvm_object_utils(uvm_logic_vector_array_axi::config_sequence)

    //configure space between packet
    int unsigned space_size_min     = 0;
    int unsigned space_size_max     = 20;

    int unsigned rdy_probability_min = 0;   // inside [0:100:ta]
    int unsigned rdy_probability_max = 100; // inside [0:100]

    function new(string name = "uvm_logic_vector_array_axi::config_sequence");
        super.new(name);
    endfunction

    function void probability_set(int unsigned min, int unsigned max);
        rdy_probability_min = min;
        rdy_probability_max = max;
    endfunction

    function void space_size_set(int unsigned min, int unsigned max);
        space_size_min = min;
        space_size_max = max;
    endfunction
endclass


class config_item extends uvm_object;
    `uvm_object_utils(uvm_logic_vector_array_axi::config_item)

    // ------------------------------------------------------------------------
    // configuration variables
    uvm_active_passive_enum active;
    string interface_name;

    enum {BASE, SPEED} lib_type;

    config_sequence seq_cfg;

    // ------------------------------------------------------------------------
    // functions
    function new (string name = "");
        super.new(name);
        lib_type = BASE;
    endfunction
endclass
