//-- config.sv: Configuration object for whole mfb env
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class config_sequence extends uvm_object;
    // this configuration is aproximation
    // there is no quratte that currently running sequence will follow this rules.
    // Guaranteed can be onli minimal space size.

    //configure space between packet
    int unsigned space_size_min     = 0;
    int unsigned space_size_max     = 200;
    // configuration of probability of rdy signal in percentige
    int unsigned rdy_probability_min = 0;   // inside [0:100:ta]
    int unsigned rdy_probability_max = 100; // inside [0:100]

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
        seq_cfg = new();
    endfunction
endclass
