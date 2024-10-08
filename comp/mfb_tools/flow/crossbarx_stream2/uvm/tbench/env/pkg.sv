// pkg.sv: Package for environment
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

`ifndef MFB_CROSSBARX_STREAM2_ENV_SV
`define MFB_CROSSBARX_STREAM2_ENV_SV

package uvm_mfb_crossbarx_stream2;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "sequencer.sv"
    `include "model.sv"
    `include "scoreboard_cmp.sv"
    `include "scoreboard.sv"
    `include "env.sv"

endpackage

`endif
