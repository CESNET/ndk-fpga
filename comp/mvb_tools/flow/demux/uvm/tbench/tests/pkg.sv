// pkg.sv: Test package
// Copyright (C) 2023-2024 CESNET z. s. p. o.
// Author: Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
//         Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

`ifndef DEMUX_TEST_SV
`define DEMUX_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    parameter ITEMS         = 4;
    parameter ITEM_WIDTH    = 8;

    parameter TX_PORTS      = 4;
    parameter DEMUX_VERSION = "register";
    parameter OUTPUT_REG_EN = 1;

    parameter CLK_PERIOD    = 4ns;
    parameter RUNS          = 15;

    `include "sequence.sv"
    `include "test.sv"

endpackage
`endif
