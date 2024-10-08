//-- pkg.sv: Package for environment
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef FIFOX_ENV_SV
`define FIFOX_ENV_SV

package uvm_asfifox;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "scoreboard.sv"
    `include "env.sv"
    `include "model.sv"

endpackage

`endif
