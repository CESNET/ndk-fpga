//-- pkg.sv: Package for environment
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef LL_DMA_ENV_SV
`define LL_DMA_ENV_SV

package uvm_dma_ll;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "registers.sv"
    `include "reg_channel.sv"
    `include "regmodel.sv"
    `include "reg_sequence.sv"

    `include "model.sv"
    `include "scoreboard.sv"
    `include "sequencer.sv"
    `include "env.sv"

endpackage

`endif
