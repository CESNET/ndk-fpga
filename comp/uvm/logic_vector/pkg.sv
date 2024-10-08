//-- pkg.sv: Package for logic vector
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef LOGIC_VECTOR_PKG
`define LOGIC_VECTOR_PKG

package uvm_logic_vector;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "config.sv"
    `include "sequence_item.sv"
    `include "meter.sv"
    `include "sequencer.sv"
    `include "sequence.sv"
    `include "monitor.sv"
    `include "agent.sv"

endpackage

`endif
