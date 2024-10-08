// pkg.sv: Package for environment
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

`ifndef FIFO_REGISTERED_ENV_SV
`define FIFO_REGISTERED_ENV_SV

package uvm_fifo_registered;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "sequencer.sv"
    `include "scoreboard.sv"
    `include "env.sv"

endpackage

`endif
