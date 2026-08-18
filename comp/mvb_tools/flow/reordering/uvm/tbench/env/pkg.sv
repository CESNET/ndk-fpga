// pkg.sv: Package for the verification environment
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
// SPDX-License-Identifier: BSD-3-Clause

`ifndef MVB_REORDERING_ENV_SV
`define MVB_REORDERING_ENV_SV

package uvm_mvb_reordering;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "model.sv"
    `include "coverage_model.sv"
    `include "scoreboard.sv"
    `include "virtual_sequencer.sv"
    `include "env.sv"

endpackage

`endif
