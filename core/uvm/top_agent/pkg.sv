//-- pkg.sv: packet environment 
//-- Copyright (C) 2024 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause 

`ifndef APP_CORE_TOP_AGENT_PKG
`define APP_CORE_TOP_AGENT_PKG

package uvm_app_core_top_agent;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "sequence_item.sv"
    `include "config.sv"

    `include "sequencer.sv"
    `include "driver.sv"
    `include "monitor.sv"
    `include "agent.sv"

    `include "sequence.sv"

endpackage

`endif
