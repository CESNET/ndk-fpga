//-- config.sv: Configuration object for whole mvb env
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class config_sequence extends uvm_object;
    `uvm_object_utils(uvm_logic_vector_mvb::config_sequence)

    uvm_common::sequence_cfg state;

    // configurate minimal and maximal space between items
    int unsigned space_size_min     =   0; // minimal space between two items it is usefull for full speed
    int unsigned space_size_max     = 200; // aproximation of maximal space size between two items is used for

    function new(string name = "uvm_logic_vector_mvb::config_sequence");
        super.new(name);
        state = null;
    endfunction


    function void space_size_set(int unsigned min, int unsigned max);
        space_size_min = min;
        space_size_max = max;
    endfunction
endclass


class config_item extends uvm_object;

    // ------------------------------------------------------------------------
    // configuration variables
    uvm_active_passive_enum active;
    string interface_name;

    //Just for RX
    config_sequence seq_cfg;

    // functions
    function new (string name = "");
        super.new(name);
        seq_cfg = null;
    endfunction
endclass
