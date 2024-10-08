/*
 * file       : config.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: Configuration file for pma agent.
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef PMA_CONFIG_SV
`define PMA_CONFIG_SV

class config_item extends uvm_object;

   // configuration variables
   uvm_active_passive_enum active;
   string interface_name;

   // functions
   function new (string name = "");
       super.new(name);
   endfunction
endclass

`endif
