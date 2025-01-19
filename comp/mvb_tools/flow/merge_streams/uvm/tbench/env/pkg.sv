// pkg.sv: Package for the verification environment
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

`ifndef MVB_MERGE_STREAMS_ENV_SV
`define MVB_MERGE_STREAMS_ENV_SV

package uvm_mvb_merge_streams;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "stream_splitter.sv"
    `include "scoreboard.sv"
    `include "virtual_sequencer.sv"
    `include "env.sv"

endpackage

`endif
