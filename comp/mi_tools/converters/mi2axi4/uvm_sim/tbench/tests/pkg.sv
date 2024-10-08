//-- pkg.sv: Test package
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef MI2AXI4LITE_TEST_SV
`define MI2AXI4LITE_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    parameter MI_DATA_WIDTH    = 32;
    parameter MI_ADDRESS_WIDTH = 32;

    parameter CLK_PERIOD        = 4ns;
    parameter RESET_CLKS        = 10;

    `include "sequence.sv"
    `include "test.sv"

endpackage
`endif
