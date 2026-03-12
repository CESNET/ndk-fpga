// config.sv: Convert PCIE to xilinx
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class config_sequence extends uvm_object;
    `ndk_object_utils(uvm_pcie::config_sequence)

    uvm_common::sequence_cfg state;

    int unsigned request_size_min; // IN DWORD
    int unsigned request_size_max; // IN DWORD
    int unsigned payload_size_min; // IN DWORD
    int unsigned payload_size_max; // IN DWORD

    function new(string name = "uvm_mfb::config_sequence");
        super.new(name);
        state = null;
        request_size_min = 1;
        request_size_max = 128; //128
        payload_size_min = request_size_min;
        payload_size_max = 64;
    endfunction
endclass



class config_item extends uvm_object;

    // ------------------------------------------------------------------------
    // Configuration variables
    //int unsigned MRRS = 4096;
    //int unsigned MP   = 4096; // xilinx 1024
    uvm_active_passive_enum active;
    string interface_name;

    // ------------------------------------------------------------------------
    // Constructor
    function new (string name = "");
        super.new(name);
    endfunction

endclass

