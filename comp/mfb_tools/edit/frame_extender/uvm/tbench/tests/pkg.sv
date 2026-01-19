// pkg.sv: Test package
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

`ifndef MFB_FRAME_EXTENDER_TEST_SV
`define MFB_FRAME_EXTENDER_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    parameter MFB_REGIONS     = 4;
    parameter MFB_REGION_SIZE = 8;
    parameter MFB_BLOCK_SIZE  = 8;
    parameter MFB_ITEM_WIDTH  = 8;
    parameter PKT_MTU         = 2**14;
    parameter MVB_FIFO_DEPTH  = 32;
    parameter MFB_FIFO_DEPTH  = 32;
    parameter USERMETA_WIDTH  = 32;

    parameter DEVICE = "AGILEX";

    parameter time CLK_PERIOD = 4ns;

    parameter int unsigned RX_MVB_ITEM_WIDTH = USERMETA_WIDTH+$clog2(PKT_MTU+1)+$clog2(PKT_MTU+1)+1+1;

    `include "extension_sequences.sv"
    `include "virtual_sequence_base.sv"
    `include "test_base.sv"
    `include "test_speed.sv"

endpackage

`endif
