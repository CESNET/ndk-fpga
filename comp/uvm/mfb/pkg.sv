//-- pkg.sv: Package for mfb interface
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef MFB_PKG
`define MFB_PKG

package uvm_mfb;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "config.sv"
    `include "sequence_item.sv"
    `include "sequencer.sv"
    `include "sequence.sv"
    `include "driver.sv"
    `include "monitor.sv"
    `include "statistic.sv"
    `include "agent.sv"
    //`include "coverage.sv"
endpackage

`endif
