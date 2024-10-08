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
    parameter ENDPOINT_TYPE      = "R_TILE";
    // FPGA device
    // STRATIX10, AGILEX, ULTRASCALE, 7SERIES
    parameter DEVICE             = "STRATIX10";
    // Depth of CQ FIFO (R-Tile only)
    parameter CQ_FIFO_ITEMS      = 512;
    // Maximum write request (payload) size (in DWORDs)
    parameter PCIE_MPS_DW        = CQ_FIFO_ITEMS/4;

    // =====================================================================
    // AXI configuration
    // =====================================================================

    parameter AXI_DATA_WIDTH     = CQ_MFB_REGIONS*CQ_MFB_REGION_SIZE*CQ_MFB_BLOCK_SIZE*CQ_MFB_ITEM_WIDTH;
    // Allowed values: 183 (USP Gen3x16); With and without straddling
    // 88 (USP Gen3x8), 85 (V7 Gen3x8); Both without straddling
    parameter AXI_CQUSER_WIDTH   = 183;
    // Allowed values: 81 (USP Gen3x16), 33 (USP Gen3x8), 33 (V7 Gen3x8)
    // All combinations are without straddling
    parameter AXI_CCUSER_WIDTH   = 81;
    // Allowed values: 137 (USP Gen3x16); With straddling
    // 62 (USP Gen3x8), 60 (V7 Gen3x8); Without straddling
    parameter AXI_RQUSER_WIDTH   = 137;
    // Allowed values: 161 (USP Gen3x16),
    // 75 (USP Gen3x8), 75 (V7 Gen3x8)
    // Both combinations with straddling
    parameter AXI_RCUSER_WIDTH   = 161;
    parameter AXI_STRADDLING     = 0;
    // latency for H-Tile is 18 cycles (20 cycles for safe)
    // latency for P-Tile is 27 cycles (30 cycles for safe)
    // latency for R-Tile is 0 cycles  (FIFO_ENABLE is disabled)
    parameter READY_LATENCY    = (ENDPOINT_TYPE == "H_TILE" || ENDPOINT_TYPE == "DUMMY") ? 20 : ((ENDPOINT_TYPE == "P_TILE") ? 30 : 0);

    // AXI META WIDTH
    parameter CQ_MFB_META_W = sv_pcie_meta_pack::PCIE_CQ_META_WIDTH;
    parameter CC_MFB_META_W = sv_pcie_meta_pack::PCIE_CC_META_WIDTH;
    parameter RQ_MFB_META_W = sv_pcie_meta_pack::PCIE_RQ_META_WIDTH;
    parameter RC_MFB_META_W = sv_pcie_meta_pack::PCIE_RC_META_WIDTH;
    // AVALON META WIDTH
                              // HDR + PREFIX + ERROR
    parameter AVST_UP_META_W   = 128 + 32 + 1;
                              // HDR + PREFIX + BAR_RANGE
    parameter AVST_DOWN_META_W = 128 + 32 + 3;

    parameter CLK_PERIOD = 5ns;

    parameter RESET_CLKS = 10;

    `include "sequence_xilinx.sv"
    `include "sequence_intel.sv"
    `include "test.sv"
    
endpackage
`endif
