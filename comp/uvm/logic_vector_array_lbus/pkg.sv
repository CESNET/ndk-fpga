// pkg.sv: Package for the environment
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

`ifndef LOGIC_VECTOR_ARRAY_LBUS_PKG
`define LOGIC_VECTOR_ARRAY_LBUS_PKG

package uvm_logic_vector_array_lbus;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "config.sv"
    `include "monitor.sv"
    `include "sequencer.sv"
    `include "sequence.sv"
    `include "env.sv"

endpackage

`endif
