/*
* file        : config.sv
 * description: configuration file for avalon rx agent
 * date       : 2020
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * Copyright (C) 2020 CESNET z. s. p. o.
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef AVST_RX_CONFIG_SV
`define AVST_RX_CONFIG_SV

//////////////////////////////////////////////////
// configuration object for AVALON RX agent.
// Import thing is: if one of parameter read_latency or read_allowance is
// lesser that one then driver is not cappable drive signals on bus
class config_item;

   ////////////////
   // configuration variables
   int unsigned read_latency = 27;
   int unsigned read_allowance = 27;

   ////////////////
   // functions
   function new ();
   endfunction
endclass

`endif
