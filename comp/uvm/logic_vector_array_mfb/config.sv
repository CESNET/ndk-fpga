//-- config.sv: Configuration object for whole mfb env
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class config_sequence extends uvm_object;
    `ndk_object_utils(uvm_logic_vector_array_mfb::config_sequence)

    uvm_common::sequence_cfg state;

    //configure space between packet
    int unsigned space_size_min     = 0;
    int unsigned space_size_max     = 200;
    // configuration of probability of rdy signal in percentige
    int unsigned rdy_probability_min = 0;   // inside [0:100:ta]
    int unsigned rdy_probability_max = 100; // inside [0:100]
    // set type of invalid values
    typedef enum {INVALID_ZERO, INVALID_UNDEF, INVALID_RAND} invalid_val_t;
    invalid_val_t generate_invalid;

    // THIS ONlY APLY TO CHECK sequence
    // NORMAL - ANYWHERE
    // PCIE   - ONLY IN FIRST REGION
    // PCIE_STRADDLING - ONLY IN FIRST REGION OR IF IN PREVIOUS REGION
    //                   EOF IS SET
    typedef enum {NORMAL, PCIE, PCIE_STRADDLING} endpoin_type_t;
    endpoin_type_t endpoint_type;

    // SRC_RDY behaviour when the word is not accepted (DST_RDY is low).
    // MFB_SRC_RDY_RELAXED - SRC_RDY can fall, the withdrawn word is sent again later
    // MFB_SRC_RDY_STRICT  - SRC_RDY must remain high until DST_RDY is high
    //                       (use it if the component requires the strict rule)
    typedef enum {MFB_SRC_RDY_RELAXED, MFB_SRC_RDY_STRICT} src_rdy_rule_t;
    src_rdy_rule_t src_rdy_rule;
    // probability [0:100] of SRC_RDY drop when the word is not accepted (only for MFB_SRC_RDY_RELAXED)
    int unsigned src_rdy_drop_probability = 10;
    // number of clock cycles with SRC_RDY low before the withdrawn word is sent again
    int unsigned src_rdy_drop_len_min     = 1;
    int unsigned src_rdy_drop_len_max     = 4;

    function new(string name = "uvm_logic_vector_array_mfb::config_sequence");
        super.new(name);
        state = null;
        generate_invalid = INVALID_RAND;
        endpoint_type = NORMAL;
        src_rdy_rule  = MFB_SRC_RDY_RELAXED;
    endfunction

    function void probability_set(int unsigned min, int unsigned max);
        rdy_probability_min = min;
        rdy_probability_max = max;
    endfunction

    function void space_size_set(int unsigned min, int unsigned max);
        space_size_min = min;
        space_size_max = max;
    endfunction

    function void src_rdy_drop_set(int unsigned probability, int unsigned len_min = 1, int unsigned len_max = 4);
        src_rdy_rule             = MFB_SRC_RDY_RELAXED;
        src_rdy_drop_probability = probability;
        src_rdy_drop_len_min     = len_min;
        src_rdy_drop_len_max     = len_max;
    endfunction
endclass


class config_item extends uvm_object;
    `ndk_object_utils(uvm_logic_vector_array_mfb::config_item)

    typedef enum {META_SOF, META_EOF, META_NONE} meta_type;
    // ------------------------------------------------------------------------
    // configuration variables
    uvm_active_passive_enum active;
    string interface_name;
    logic coverage;
    meta_type meta_behav = META_NONE;
    // Metadata behaviour -----------------------------
    // META_SOF means that metadata are paired with SOF position
    // META_EOF means that metadata are paired with EOF position
    // META_NONE DONT CARE IF META_WIDTH = 0
    // ------------------------------------------------

    // This set only library type.
    // Checking and stradling add by seq_cfg.generate_invalid
    enum {BASE, SPEED, PCIE} lib_type;
    config_sequence seq_cfg;

    // ------------------------------------------------------------------------
    // functions
    function new (string name = "");
        super.new(name);
        seq_cfg = new();
        coverage = 0;
        lib_type = BASE;
    endfunction

    function void set_pcie(logic straddling = 0);
        lib_type = PCIE;
        if (straddling == 1) begin
            seq_cfg.endpoint_type = config_sequence::PCIE_STRADDLING;
        end else begin
            seq_cfg.endpoint_type = config_sequence::PCIE;
        end
    endfunction
endclass
