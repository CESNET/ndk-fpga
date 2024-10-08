// pkg.sv: Package for environment
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kriz <danielkriz@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


`ifndef ITEMS_VALID_ENV_SV
`define ITEMS_VALID_ENV_SV

package uvm_items_valid;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "sequencer.sv"
    `include "sequence.sv"
    `include "driver.sv"
    `include "model.sv"
    `include "scoreboard.sv"
    `include "env.sv"

endpackage

`endif
