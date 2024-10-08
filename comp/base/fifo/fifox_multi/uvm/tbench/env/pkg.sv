// pkg.sv: Package for environment
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

`ifndef FIFOX_MULTI_ENV_SV
`define FIFOX_MULTI_ENV_SV

package uvm_fifox_multi;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "sequencer.sv"
    `include "status_model.sv"
    `include "scoreboard.sv"
    `include "env.sv"

endpackage

`endif
