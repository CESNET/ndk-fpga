//-- pkg.sv: Package for environment
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef SPLITTER_SIMPLE_GEN_ENV_SV
`define SPLITTER_SIMPLE_GEN_ENV_SV

package uvm_splitter_simple;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `uvm_analysis_imp_decl(_reset)

    //`include "sequencer.sv"
    `include "model.sv"
    `include "scoreboard.sv"
    `include "env.sv"

endpackage

`endif
