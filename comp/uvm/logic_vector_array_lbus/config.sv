// config.sv: A configuration object for the environment
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class config_item extends uvm_object;
    `uvm_object_utils(uvm_logic_vector_array_lbus::config_item)

    // ----------------------- //
    // Configuration variables //
    // ----------------------- //

    uvm_active_passive_enum active;
    string interface_name;

    enum {BASE, SPEED} lib_type;

    // Constructor
    function new(string name = "config_item");
        super.new(name);
        lib_type = BASE;
    endfunction

endclass
