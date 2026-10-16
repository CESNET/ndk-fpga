//-- config.sv: Configuration object for whole mvb env
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class config_sequence extends uvm_object;
    `ndk_object_utils(uvm_logic_vector_mvb::config_sequence)

    uvm_common::sequence_cfg state;

    // configurate minimal and maximal space between items
    int unsigned space_size_min     =   0; // minimal space between two items it is usefull for full speed
    int unsigned space_size_max     = 200; // aproximation of maximal space size between two items is used for

    typedef enum {INVALID_ZERO, INVALID_UNDEF, INVALID_RAND} invalid_val_t;
    invalid_val_t generate_invalid;

    // SRC_RDY behaviour when the word is not accepted (DST_RDY is low).
    // MVB_SRC_RDY_RELAXED - SRC_RDY can fall, the withdrawn word is sent again later
    // MVB_SRC_RDY_STRICT  - SRC_RDY must remain high until DST_RDY is high
    //                       (use it if the component requires the strict rule)
    typedef enum {MVB_SRC_RDY_RELAXED, MVB_SRC_RDY_STRICT} src_rdy_rule_t;
    src_rdy_rule_t src_rdy_rule;
    // probability [0:100] of SRC_RDY drop when the word is not accepted (only for MVB_SRC_RDY_RELAXED)
    int unsigned src_rdy_drop_probability = 10;
    // number of clock cycles with SRC_RDY low before the withdrawn word is sent again
    int unsigned src_rdy_drop_len_min     = 1;
    int unsigned src_rdy_drop_len_max     = 4;

    function new(string name = "uvm_logic_vector_mvb::config_sequence");
        super.new(name);
        state = null;
        generate_invalid = INVALID_RAND;
        src_rdy_rule     = MVB_SRC_RDY_RELAXED;
    endfunction


    function void space_size_set(int unsigned min, int unsigned max);
        space_size_min = min;
        space_size_max = max;
    endfunction

    function void src_rdy_drop_set(int unsigned probability, int unsigned len_min = 1, int unsigned len_max = 4);
        src_rdy_rule             = MVB_SRC_RDY_RELAXED;
        src_rdy_drop_probability = probability;
        src_rdy_drop_len_min     = len_min;
        src_rdy_drop_len_max     = len_max;
    endfunction
endclass


class config_item extends uvm_object;

    // ------------------------------------------------------------------------
    // configuration variables
    uvm_active_passive_enum active;
    logic coverage;
    string interface_name;

    enum {BASE, SPEED} lib_type;
    //Just for RX
    config_sequence seq_cfg;

    // functions
    function new (string name = "");
        super.new(name);
        seq_cfg = null;
        coverage = 0;
        lib_type = BASE;
    endfunction
endclass
