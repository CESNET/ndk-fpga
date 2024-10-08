// pkg.sv: Package for environment
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kříž <danielkriz@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


`ifndef METADATA_INSERTOR_ENV_SV
`define METADATA_INSERTOR_ENV_SV

package uvm_metadata_insertor;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "sequencer.sv"
    `include "model.sv"
    `include "scoreboard.sv"
    `include "env.sv"

endpackage

`endif
