//-- pkg.sv: test packages
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef NETWORK_MOD_ENV_SV
`define NETWORK_MOD_ENV_SV

package uvm_network_mod_env;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "registers.sv"
    `include "regmodel.sv"

    `include "sequencer.sv"
    `include "model.sv"
    `include "scoreboard_cmp.sv"
    `include "scoreboard.sv"
    `include "env.sv"

    `include "reg_sequence.sv"
    `include "sequence_eth.sv"
    `include "sequence.sv"
endpackage
`endif

