// pkg.sv: Package for environment
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
// SPDX-License-Identifier: BSD-3-Clause

`ifndef PACKET_DELAYER_ENV_SV
`define PACKET_DELAYER_ENV_SV

package uvm_packet_delayer;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    // Stimulus: TIME_RESET agent and the {META, TS} sequence
    `include "sequence_tb.sv"
    `include "virtual_sequencer.sv"

    // Checking: items with the expected release time, time-aware comparers,
    // reference model and scoreboard
    `include "delayer_item.sv"
    `include "comparer_time.sv"
    `include "model.sv"
    `include "scoreboard.sv"

    `include "env.sv"

endpackage

`endif
