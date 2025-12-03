//-- pkg.sv: package with all tests
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef RX_DMA_CALYPTE_TEST_SV
`define RX_DMA_CALYPTE_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    parameter MI_WIDTH         = 32;

    parameter USR_MFB_REGIONS     = 1;
    parameter USR_MFB_REGION_SIZE = 4;
    parameter USR_MFB_BLOCK_SIZE  = 8;
    parameter USR_MFB_ITEM_WIDTH  = 8;

    parameter PCIE_RQ_REGIONS     = 1;
    parameter PCIE_RQ_REGION_SIZE = 1;
    parameter PCIE_RQ_BLOCK_SIZE  = 8;
    parameter PCIE_RQ_ITEM_WIDTH  = 32;
    parameter PCIE_RQ_META_WIDTH  = sv_pcie_meta_pack::PCIE_RQ_META_WIDTH;

    parameter CHANNELS       = 4;
    parameter POINTER_WIDTH  = 16;
    parameter SW_ADDR_WIDTH  = 64;
    parameter CNTRS_WIDTH    = 64;
    parameter PKT_SIZE_MAX   = 2**12;
    parameter TRBUF_REG_EN   = 1'b1;
    parameter PERF_CNTR_EN   = 1'b0;

    parameter DEVICE = "ULTRASCALE";

    parameter CLK_PERIOD = 4ns;

    `include "sequence.sv"
    `include "base.sv"
    `include "speed.sv"

endpackage
`endif
