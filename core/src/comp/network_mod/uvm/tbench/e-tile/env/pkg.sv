// pkg.sv: Package for Intel E-Tile environment
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

`ifndef NETWORK_MOD_E_TILE_ENV_SV
`define NETWORK_MOD_E_TILE_ENV_SV

package uvm_network_mod_e_tile_env;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "sequencer_port.sv"
    `include "sequence.sv"
    `include "env.sv"

endpackage

`endif
