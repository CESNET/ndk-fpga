//-- config.sv: Configuration object for AXI env
//-- Copyright (C) 2025 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


class config_sequence extends uvm_axi::config_sequence;
    `ndk_object_utils(uvm_pcie_axi::config_sequence)

    uvm_pcie::bar_config bar;

    function new (string name = "");
        super.new(name);
        bar = null;
    endfunction

endclass

