//-- config.sv: Config file for logic vector agent
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause
class config_sequence extends uvm_object;
    `uvm_object_utils(uvm_logic_vector::config_sequence)

    function new (string name = "uvm_logic_vector_array::config_sequence");
        super.new(name);
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
