// pkg.sv: Package for environment
// MVB_FORK UVM verification
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

`ifndef MVB_FORK_UVM_ENV_SV
`define MVB_FORK_UVM_ENV_SV

package uvm_mvb_fork;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "sequencer.sv"
    `include "model.sv"
    `include "scoreboard.sv"
    `include "env.sv"

endpackage

`endif
