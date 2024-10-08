// config.sv: Configuration object for the LBUS agent
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class config_sequence extends uvm_object;
    `uvm_object_utils(uvm_lbus::config_sequence)

    // ----------------------- //
    // Configuration variables //
    // ----------------------- //

    int unsigned rdy_probability_max = 100;
    int unsigned rdy_probability_min = 0;

    // Constructor
    function new(string name = "config_sequence");
        super.new(name);
    endfunction

    function void probability_set(int unsigned min, int unsigned max);
        rdy_probability_min = min;
        rdy_probability_max = max;
    endfunction

endclass

class config_item extends uvm_object;
    `uvm_object_utils(uvm_lbus::config_item)

    // ----------------------- //
    // Configuration variables //
    // ----------------------- //

    uvm_active_passive_enum active;
    string interface_name;

    // Constructor
    function new(string name = "config_item");
        super.new(name);
    endfunction

endclass
