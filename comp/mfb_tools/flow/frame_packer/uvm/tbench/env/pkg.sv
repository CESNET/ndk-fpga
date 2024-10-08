// pkg.sv: Package for environment
// Copyright (C) 2024 CESNET z. s. p. o.
// Author:   David Beneš <xbenes52@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

`ifndef FRAMEPACKER_ENV_SV
`define FRAMEPACKER_ENV_SV

package uvm_framepacker;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "sequence_tb.sv"
    `include "sequencer.sv"
    `include "generator.sv"
    `include "model.sv"
    `include "scoreboard_cmp.sv"
    `include "scoreboard.sv"
    `include "env.sv"

endpackage

`endif
