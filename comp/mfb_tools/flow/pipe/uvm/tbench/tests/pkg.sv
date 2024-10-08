//-- pkg.sv: Test package
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author:   David Beneš <xbenes52@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef MFB_PIPE_TEST_SV
`define MFB_PIPE_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    //MFB parameters
    parameter REGIONS       = 4;
    parameter REGION_SIZE   = 8;
    parameter BLOCK_SIZE    = 8;
    parameter ITEM_WIDTH    = 8;
    //MFB META parameter ... Zero is not supported (yet)
    parameter META_WIDTH    = 8;

    parameter FAKE_PIPE     = 0;
    parameter USE_DST_RDY   = 1;
    parameter PIPE_TYPE     = "SHREG";
    parameter DEVICE        = "ULTRASCALE";

    parameter CLK_PERIOD = 4ns;

    `include "sequence.sv"
    `include "test.sv"

endpackage
`endif
