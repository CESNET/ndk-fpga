//-- config.sv: Configuration object for AVST env
//-- Copyright (C) 2025 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class config_sequence extends uvm_avst::config_sequence;
    `uvm_object_utils(uvm_pcie_avst::config_sequence)

    int unsigned rdy_latency;
    uvm_pcie::bar_config bar;

    function new(string name = "uvm_logic_vector_array_mfb::config_sequence");
        super.new(name);
        rdy_latency = 0;
        bar = null;
    endfunction
endclass



