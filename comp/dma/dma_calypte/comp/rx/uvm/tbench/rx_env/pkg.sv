//-- pkg.sv
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef RX_ENV_PKG
`define RX_ENV_PKG

package uvm_dma_ll_rx;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "config.sv"
    `include "sequencer.sv"
    `include "sequence.sv"
    `include "driver.sv"
    `include "env.sv"

endpackage

`endif
