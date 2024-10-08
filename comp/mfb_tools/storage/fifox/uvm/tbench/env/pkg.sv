// pkg.sv: Package for environment
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Mikuláš Brázda <xbrazd21@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


`ifndef UVM_MFB_FIFOX
`define UVM_MFB_FIFOX

package uvm_mfb_fifox;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "sequencer.sv"
    `include "model.sv"
    `include "scoreboard.sv"
    `include "env.sv"

endpackage

`endif
