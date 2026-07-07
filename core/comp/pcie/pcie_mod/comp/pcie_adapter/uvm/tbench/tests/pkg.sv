//-- pkg.sv: Test package
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef PCIE_AVST2MFB_TEST_SV
`define PCIE_AVST2MFB_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    // =====================================================================
    // MFB configuration
    // For Intel configuration have to be same
    // =====================================================================
    // CQ MFB
    // Supported configurations are: (2,1,8,32), (1,1,8,32)
    parameter CQ_MFB_REGIONS     = 2;
    parameter CQ_MFB_REGION_SIZE = 1;
    parameter CQ_MFB_BLOCK_SIZE  = 8;
    parameter CQ_MFB_ITEM_WIDTH  = 32;
    // RC MFB
    // Supported configuration is 4,1,4,32 for PCIe on UltraScale+
    // Supported configuration is 2,1,4,32 for PCIe on Virtex 7 Series
    parameter RC_MFB_REGIONS     = 2;
    parameter RC_MFB_REGION_SIZE = 1;
    parameter RC_MFB_BLOCK_SIZE  = 8;
    parameter RC_MFB_ITEM_WIDTH  = 32;
    // CC MFB
    // Supported configuration is: (2,1,8,32), (1,1,8,32)
    parameter CC_MFB_REGIONS     = 2;
    parameter CC_MFB_REGION_SIZE = 1;
    parameter CC_MFB_BLOCK_SIZE  = 8;
    parameter CC_MFB_ITEM_WIDTH  = 32;
    // RQ MFB
    // Supported configurations are: (2,1,8,32), (1,1,8,32)
    parameter RQ_MFB_REGIONS     = 2;
    parameter RQ_MFB_REGION_SIZE = 1;
    parameter RQ_MFB_BLOCK_SIZE  = 8;
    parameter RQ_MFB_ITEM_WIDTH  = 32;

    // =====================================================================
    // Common configuration
    // =====================================================================
    // Connected PCIe endpoint type
    // P_TILE, R_TILE
    parameter ENDPOINT_TYPE      = "P_TILE";
    // FPGA device
    // STRATIX10, AGILEX, ULTRASCALE
    parameter DEVICE             = "STRATIX10";
    //parameter DEVICE             = "ULTRASCALE";
    // Depth of CQ FIFO (R-Tile only)
    parameter CQ_FIFO_ITEMS      = 512;
    // Maximum write request (payload) size (in DWORDs)
    parameter PCIE_MPS_DW        = CQ_FIFO_ITEMS/4;

    // =====================================================================
    // AXI configuration
    // =====================================================================

    // AXI_ITEMS = {2, 4, 8, 16}
    parameter STRADDLING     = 0;
    // latency for H-Tile is 18 cycles (20 cycles for safe)
    // latency for P-Tile is 27 cycles (30 cycles for safe)
    // latency for R-Tile is 0 cycles  (FIFO_ENABLE is disabled)
    parameter READY_LATENCY = (ENDPOINT_TYPE == "H_TILE" || ENDPOINT_TYPE == "DUMMY") ?
        20 : ((ENDPOINT_TYPE == "P_TILE") ? 30 : 0);

    parameter CLK_PERIOD = 5ns;

    parameter RESET_CLKS = 10;

    `include "test.sv"

endpackage
`endif
