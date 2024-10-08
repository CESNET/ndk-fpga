// config.sv: Configuration object for AVMM agent
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

`ifndef AVMM_CONFIG_SV
`define AVMM_CONFIG_SV

class config_sequence extends uvm_object;
    `uvm_object_utils(uvm_avmm::config_sequence)

    // ----------------------- //
    // Configuration variables //
    // ----------------------- //

    int unsigned transaction_count_min = 1000;
    int unsigned transaction_count_max = 10000;

    time latency_min = 50ns;
    time latency_max = 150ns;

    int unsigned excited_count_min = 40;
    int unsigned excited_count_max = 100;

    function new(string name = "config_sequence");
        super.new(name);
    endfunction

    function void set_transaction_count(int unsigned min, int unsigned max);
        transaction_count_min = min;
        transaction_count_max = max;
    endfunction

    function void set_latency(int unsigned min, int unsigned max);
        latency_min = min;
        latency_max = max;
    endfunction

    function void set_excited_count(int unsigned min, int unsigned max);
        excited_count_min = min;
        excited_count_max = max;
    endfunction

endclass

class config_item extends uvm_object;

    // ----------------------- //
    // Configuration variables //
    // ----------------------- //

    uvm_active_passive_enum active;
    string interface_name;

    // Memory model configuration
    typedef enum {
        NULL,
        RANDOM
    } generated_memory_file_type_e;

    logic generated_memory_file = 1;
    generated_memory_file_type_e generated_memory_file_type = NULL;
    string memory_filepath = "";

endclass

`endif
