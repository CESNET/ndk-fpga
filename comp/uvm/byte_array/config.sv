/*
 * file       : config.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: Configuration file for byte array agent.
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef BYTE_ARRAY_CONFIG_SV
`define BYTE_ARRAY_CONFIG_SV

class config_sequence extends uvm_object;
    // this configuration is aproximation
    // there is no quratte that currently running sequence will follow this rules.

    // Default value is ethernet MTU (64-1500)
    int unsigned array_size_min = 64;   // size have to be bigger than zero
    int unsigned array_size_max = 1500;

    // this configuration works for all sequences run by sequences library.
    // if two sequences will run by sequences library then 20 to 400 transactios
    // are going to be generated
    int unsigned transaction_count_min = 10;   // size have to be bigger than zero
    int unsigned transaction_count_max = 200;

    function void array_size_set(int unsigned min, int unsigned max);
        array_size_min = min;
        array_size_max = max;
    endfunction

    function void transaction_count_set(int unsigned min, int unsigned max);
        transaction_count_min = min;
        transaction_count_max = max;
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
