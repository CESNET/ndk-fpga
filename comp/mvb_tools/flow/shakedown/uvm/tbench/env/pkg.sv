// pkg.sv: Package for the verification environment
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

`ifndef MVB_SHAKEDOWN_ENV_SV
`define MVB_SHAKEDOWN_ENV_SV

package uvm_mvb_shakedown;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "read_command_item.sv"
    `include "model.sv"
    `include "hl_coverage_model.sv"
    `include "ll_coverage_model.sv"
    `include "scoreboard.sv"
    `include "activity_detector.sv"
    `include "virtual_sequencer.sv"
    `include "env.sv"

endpackage

`endif
