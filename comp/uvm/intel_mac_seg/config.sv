/*
 * file       : config.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: configuration for intel seq mac agent
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

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

