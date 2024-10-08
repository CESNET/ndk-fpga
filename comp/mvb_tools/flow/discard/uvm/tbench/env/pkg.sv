//-- pkg.sv: Package for environment
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author:   Jakub Cabal <cabal@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef FIFOX_ENV_SV
`define FIFOX_ENV_SV

package uvm_discard;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "sequencer.sv"
    `include "model.sv"
    `include "scoreboard.sv"
    `include "env.sv"

endpackage

`endif
