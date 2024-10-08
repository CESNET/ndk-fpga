//-- pkg.sv: Package for AVST credit control interface
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause 

`ifndef CRDT_PKG
`define CRDT_PKG

package uvm_crdt;
    
    `include "uvm_macros.svh"
    import uvm_pkg::*;
   
    `include "config.sv"
    `include "sequence_item.sv"
    `include "sequencer.sv"
    `include "sequence.sv"
    `include "driver.sv"
    `include "monitor.sv"
    `include "agent.sv"
endpackage

`endif
