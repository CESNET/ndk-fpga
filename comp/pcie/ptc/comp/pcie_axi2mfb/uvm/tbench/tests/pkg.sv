// pkg.sv: Test package
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


`ifndef MFB_TO_LBUS_ADAPTER_TEST_SV
`define MFB_TO_LBUS_ADAPTER_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;
    // =======================================================================
    // Target device specification
    // =======================================================================
    // Supported devices: "7SERIES", "ULTRASCALE"
    parameter DEVICE          = "ULTRASCALE";
    // =======================================================================
    // MFB BUS CONFIGURATION:
    // =======================================================================
    // Supported configuration is MFB(4,1,4,32) for PCIe on UltraScale+
    // Supported configuration is MFB(2,1,4,32) for PCIe on Virtex 7 Series
    parameter REGIONS     = 4;
    parameter REGION_SIZE = 1;
    parameter BLOCK_SIZE  = 4;
    parameter ITEM_WIDTH  = 32;
    // =======================================================================
    // AXI BUS CONFIGURATION:
    // =======================================================================
    // DATA=512, RC=161 for Gen3x16 PCIe (Virtex UltraScale+) - with straddling!
    // DATA=256, RC=70  for Gen3x16 PCIe (Virtex 7 Series) - with straddling!
    parameter DATA_WIDTH      = 512;
    parameter TUSER_WIDTH     = 161;
    // Do not change
    parameter STRADDLING      = 1;

    parameter DRAIN_TIME         = 20ns;
    parameter TRANSACTION_COUNT  = 1000000;

    parameter CLK_PERIOD         = 2500ps;

    parameter RESET_CLKS         = 10;

    `include "sequence.sv"
    `include "test.sv"
endpackage
`endif
