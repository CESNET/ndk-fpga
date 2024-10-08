// pkg.sv: Test package
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


`ifndef MVB2MFB_TEST_SV
`define MVB2MFB_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    parameter CLK_PERIOD         = 4ns;
    parameter RESET_CLKS         = 10;

    `include "sequence.sv"
    `include "test.sv"
    `include "speed.sv"
endpackage
`endif
