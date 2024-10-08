// pkg.sv: Package for environment
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

`ifndef MVB_MERGE_STREAMS_ORDERED_ENV_SV
`define MVB_MERGE_STREAMS_ORDERED_ENV_SV

package uvm_mvb_merge_streams_ordered;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "sequencer.sv"
    `include "model.sv"
    `include "scoreboard.sv"
    `include "env.sv"
endpackage

`endif
