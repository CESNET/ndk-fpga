//-- pkg.sv:
//-- Copyright (C) 2026 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef LOGIC_VECTOR_ARRAY_AXI_PKG
`define LOGIC_VECTOR_ARRAY_AXI_PKG

package uvm_logic_vector_array_axi;

    `include "ndk_macros.svh"
    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "config.sv"
    `include "monitor.sv"
    `include "sequencer.sv"
    `include "sequence.sv"
    `include "sequence_lib.sv"
    `include "env.sv"

endpackage

`endif
