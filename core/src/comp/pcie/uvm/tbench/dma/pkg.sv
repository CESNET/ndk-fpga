// pkg.sv: Package for environment dma environment
// Copyright (C) 2024 CESNET z. s. p. o.
// Author:  Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

`ifndef DMA_RQ_SV
`define DMA_RQ_SV

package uvm_dma;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "config_item.sv"
    `include "sequence_item.sv"
    `include "sequence.sv"

    `include "driver.sv"
    `include "monitor.sv"
    `include "sequencer.sv"
    `include "env.sv"
endpackage

`endif
