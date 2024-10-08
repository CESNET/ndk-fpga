//-- config.sv: Configuration object for whole app verification
//-- Copyright (C) 2024 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class config_sequence_eth extends uvm_packet_generators::config_sequence;

    rand time time_start;

    function new ();
        super.new();
        time_start = 0ns;
    endfunction
endclass


class config_item extends uvm_object;

    typedef enum {CMP_ORDERED, CMP_UNORDERED, CMP_TAGGED} cmp_type;
    // ------------------------------------------------------------------------
    // configuration variables
    cmp_type compare_eth;
    cmp_type compare_dma;

    // ------------------------------------------------------------------------
    // functions
    function new (string name = "");
        super.new(name);
        compare_eth = CMP_ORDERED;
        compare_dma = CMP_ORDERED;
    endfunction
endclass



