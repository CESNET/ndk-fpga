//-- config.sv: Configuration object for whole mfb env
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class config_sequence extends uvm_object;
    `uvm_object_utils(uvm_logic_vector_array_avst::config_sequence)

    uvm_common::sequence_cfg state;

    //configure space between packet
    int unsigned space_size_min     = 0;
    int unsigned space_size_max     = 200;
    // configuration of probability of rdy signal in percentige
    int unsigned rdy_probability_min = 0;   // inside [0:100:ta]
    int unsigned rdy_probability_max = 100; // inside [0:100]
    // Straddling is used only with seq_type == "PCIE"
    logic straddling                 = 0;

    function new(string name = "uvm_logic_vector_array_avst::config_sequence");
        super.new(name);
        state = null;
    endfunction

    function void probability_set(int unsigned min, int unsigned max);
        rdy_probability_min = min;
        rdy_probability_max = max;
    endfunction

    function void straddling_set(logic value);
        straddling = value;
    endfunction

    function void space_size_set(int unsigned min, int unsigned max);
        space_size_min = min;
        space_size_max = max;
    endfunction
endclass


class config_item extends uvm_object;

    typedef enum {META_SOF, META_EOF, META_NONE} meta_type;
    // ------------------------------------------------------------------------
    // configuration variables
    uvm_active_passive_enum active;
    string interface_name;
    meta_type meta_behav = META_NONE;  // Metadata behaviour -----------------------------
                                // META_SOF means that metadata are paired with SOF position
                                // META_EOF means that metadata are paired with EOF position
                                // META_NONE DONT CARE IF META_WIDTH = 0
                                // ------------------------------------------------

    config_sequence seq_cfg;

    // ------------------------------------------------------------------------
    // functions
    function new (string name = "");
        super.new(name);
    endfunction
endclass
