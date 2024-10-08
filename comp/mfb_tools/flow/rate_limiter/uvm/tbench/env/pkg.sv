// pkg.sv: Package for environment
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Tomas Hak <xhakto01@vut.cz>

// SPDX-License-Identifier: BSD-3-Clause

`ifndef RATE_LIMITER_ENV_SV
`define RATE_LIMITER_ENV_SV

package uvm_rate_limiter;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "registers.sv"
    `include "regmodel.sv"

    `include "sequencer.sv"
    `include "scoreboard.sv"
    `include "env.sv"

endpackage

`endif
