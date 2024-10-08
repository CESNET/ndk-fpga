//-- pkg.sv: Package for mvb rx interface
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef BYTE_ARRAY_INTEL_MAC_SEG_PKG
`define BYTE_ARRAY_INTEL_MAC_SEG_PKG

package uvm_logic_vector_array_intel_mac_seg;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "config.sv"
    `include "sequencer.sv"
    `include "sequence.sv"
    `include "monitor_byte_array.sv"
    `include "monitor_logic_vector.sv"
    `include "env.sv"
endpackage

`endif
