/*
 * file       : config.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: Configuration file for byte array agent.
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef SIZE_GEN_CONFIG_SV
`define SIZE_GEN_CONFIG_SV


class config_sequence extends uvm_object;
    `uvm_object_utils(uvm_logic_vector_array::config_sequence)

    // Default value is ethernet MTU (64-1500)
    int unsigned array_size_min = 64;   // size have to be bigger than zero
    int unsigned array_size_max = 1500;

    function new (string name = "uvm_logic_vector_array::config_sequence");
        super.new(name);
    endfunction

    function void array_size_set(int unsigned min, int unsigned max);
        array_size_min = min;
        array_size_max = max;
    endfunction
endclass

class config_item extends uvm_object;

   ////////////////
   // configuration variables
   uvm_active_passive_enum active;

   ////////////////
   // functions
   function new (string name = "");
       super.new(name);
   endfunction
endclass

`endif
