// pkg.sv: Test package
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

`ifndef MFB_FRAME_TRIMMER_TEST_SV
`define MFB_FRAME_TRIMMER_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    parameter REGIONS     = 4;
    parameter REGION_SIZE = 8;
    parameter BLOCK_SIZE  = 8;
    parameter ITEM_WIDTH  = 8;
    parameter META_WIDTH  = 8;
    parameter PKT_MTU     = 2**14;

    parameter DEVICE = "AGILEX";

    parameter time CLK_PERIOD = 4ns;

    `include "trim_sequences.sv"
    `include "virtual_sequence_base.sv"
    `include "test_base.sv"
    `include "virtual_sequence_speed.sv"
    `include "test_speed.sv"

endpackage

`endif
