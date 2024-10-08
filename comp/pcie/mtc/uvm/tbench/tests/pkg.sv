//-- pkg.sv: package with all tests
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef MTC_TEST_SV
`define MTC_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    // MFB configuration
    parameter MFB_REGIONS       = 2;
    parameter MFB_REGION_SIZE   = 1;
    parameter MFB_BLOCK_SIZE    = 8;
    parameter MFB_ITEM_WIDTH    = 32;

    // BAR BASE ADDRESS configuration
    parameter BAR0_BASE_ADDR    = 32'h01000000;
    parameter BAR1_BASE_ADDR    = 32'h02000000;
    parameter BAR2_BASE_ADDR    = 32'h03000000;
    parameter BAR3_BASE_ADDR    = 32'h04000000;
    parameter BAR4_BASE_ADDR    = 32'h05000000;
    parameter BAR5_BASE_ADDR    = 32'h06000000;
    parameter EXP_ROM_BASE_ADDR = 32'h0A000000;

    // Pipes enables
    parameter CC_PIPE           = 1;
    parameter CQ_PIPE           = 1;
    parameter MI_PIPE           = 1;

    // MI configuration
    parameter MI_DATA_WIDTH     = 32;
    parameter MI_ADDR_WIDTH     = 32;

    // Device specifics
    parameter DEVICE            = "STRATIX10";
    parameter ENDPOINT_TYPE     = "P_TILE";

    // Verification parameters
    parameter CLK_PERIOD        = 10ns;
    parameter PCIE_LEN_MIN      = 1;
    parameter PCIE_LEN_MAX      = 1024;
    parameter BYTES_LEN_MAX     = PCIE_LEN_MAX*4;

    `include "sequence.sv"
    `include "base.sv"
    `include "speed.sv"

endpackage
`endif
