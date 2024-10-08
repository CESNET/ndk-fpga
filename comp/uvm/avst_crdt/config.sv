// config.sv: Configuration object for AVST credit control agent
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

`ifndef AVST_CRDT_CONFIG_SV
`define AVST_CRDT_CONFIG_SV

class config_item extends uvm_object;
    `uvm_object_utils(uvm_avst_crdt::config_item)

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

`endif
