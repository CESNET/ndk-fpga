/*
 * file       : pkg.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: mi package. configuration of designs
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


`ifndef MI_PKG
`define MI_PKG

package uvm_mi;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "config.sv"

    `include "sequence_item.sv"
    `include "sequencer.sv"
    `include "driver.sv"
    `include "monitor.sv"
    `include "agent.sv"

    `include "sequence.sv"

    // CLASSES FOR SIMPLIFY ACCESSING REGISTER MODEL
    // TROUGH MI
    `include "reg2bus_monitor.sv"
    `include "reg2bus_convert.sv"
    `include "regmodel.sv"
endpackage


`endif
