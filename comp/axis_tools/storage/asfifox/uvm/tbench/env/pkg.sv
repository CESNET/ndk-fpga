//-- pkg.sv: Package for environment
//-- Copyright (C) 2026 CESNET z. s. p. o.
//-- Author(s): Tomáš Neckař <xneckat00@stud.fit.vut.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


`ifndef ASFIFOX_ENV_SV
`define ASFIFOX_ENV_SV

package uvm_asfifox;

    `include "ndk_macros.svh"
    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "config.sv"
    `include "sequence.sv"

    `include "sequencer.sv"
    `include "model.sv"
    `include "scoreboard.sv"
    `include "env.sv"

endpackage
`endif
