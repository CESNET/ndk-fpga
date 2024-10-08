//-- pkg.sv: package with all tests
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef SPLITTER_SIMPLE_TEST_SV
`define SPLITTER_SIMPLE_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    parameter MI_WIDTH         = 32;

    parameter USER_REGIONS     = 1;
    parameter USER_REGION_SIZE = 8;
    parameter USER_BLOCK_SIZE  = 8;
    parameter USER_ITEM_WIDTH  = 8;

    parameter PCIE_UP_REGIONS     = 2;
    parameter PCIE_UP_REGION_SIZE = 1;
    parameter PCIE_UP_BLOCK_SIZE  = 8;
    parameter PCIE_UP_ITEM_WIDTH  = 32;
    parameter PCIE_UP_META_WIDTH  = sv_pcie_meta_pack::PCIE_RQ_META_WIDTH;

    parameter CHANNELS       = 4;
    parameter POINTER_WIDTH  = 16;
    parameter SW_ADDR_WIDTH  = 64;
    parameter CNTRS_WIDTH    = 64;
    parameter PKT_SIZE_MAX   = 2**12;
    parameter OPT_BUFF       = 1'b0;
    parameter TRBUF_REG_EN   = 1'b1;

    parameter DEVICE = "ULTRASCALE";

    parameter CLK_PERIOD = 4ns;

    `include "sequence.sv"
    `include "base.sv"
    `include "speed.sv"

endpackage
`endif
