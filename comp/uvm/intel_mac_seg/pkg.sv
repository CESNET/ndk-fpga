//-- pkg.sv: Package for mvb rx interface
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef INTEL_MAC_SEG_PKG
`define INTEL_MAC_SEG_PKG

package uvm_intel_mac_seg;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "sequence_item.sv"
    `include "sequencer.sv"
    `include "driver.sv"
    `include "monitor.sv"
    `include "statistic.sv"
    `include "config.sv"
    `include "agent.sv"

    `include "sequence.sv"
endpackage

`endif
