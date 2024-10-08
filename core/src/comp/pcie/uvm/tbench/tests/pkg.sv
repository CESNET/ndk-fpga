//-- pkg.sv: Test package
//-- Copyright (C) 2024 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef PCIE_AVST2MFB_TEST_SV
`define PCIE_AVST2MFB_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    // =====================================================================
    // BAR BASE ADDRESS configuration
    // =====================================================================
    parameter BAR0_BASE_ADDR    = 32'h01000000;
    parameter BAR1_BASE_ADDR    = 32'h02000000;
    parameter BAR2_BASE_ADDR    = 32'h03000000;
    parameter BAR3_BASE_ADDR    = 32'h04000000;
    parameter BAR4_BASE_ADDR    = 32'h05000000;
    parameter BAR5_BASE_ADDR    = 32'h06000000;
    parameter EXP_ROM_BASE_ADDR = 32'h0A000000;
    // =====================================================================
    // MFB configuration
    // For Intel configuration have to be same
    // =====================================================================
    // RQ MFB
    // Supported configurations are: (2,1,8,32), (1,1,8,32)
    parameter RQ_MFB_REGIONS     = 2;
    parameter RQ_MFB_REGION_SIZE = 1;
    parameter RQ_MFB_BLOCK_SIZE  = 8;
   // RC MFB
    // Supported configuration is 4,1,4,32 for PCIe on UltraScale+
    // Supported configuration is 2,1,4,32 for PCIe on Virtex 7 Series
    parameter RC_MFB_REGIONS     = 2;
    parameter RC_MFB_REGION_SIZE = 1;
    parameter RC_MFB_BLOCK_SIZE  = 8;
     // CQ MFB
    // Supported configurations are: (2,1,8,32), (1,1,8,32)
    parameter CQ_MFB_REGIONS     = 2;
    parameter CQ_MFB_REGION_SIZE = 1;
    parameter CQ_MFB_BLOCK_SIZE  = 8;
   // CC MFB
    // Supported configuration is: (2,1,8,32), (1,1,8,32)
    parameter CC_MFB_REGIONS     = 2;
    parameter CC_MFB_REGION_SIZE = 1;
    parameter CC_MFB_BLOCK_SIZE  = 8;
     // AVALON META WIDTH
    parameter ITEM_WIDTH  = 32;


                              // HDR + PREFIX + ERROR
    parameter AVST_UP_META_W   = 128 + 32 + 1;
                              // HDR + PREFIX + BAR_RANGE
    parameter AVST_DOWN_META_W = 128 + 32 + 3;

    // PCIE HEADER WIDTHS
    parameter PCIE_UPHDR_WIDTH      = 128;
    parameter PCIE_DOWNHDR_WIDTH    = 3*4*8;
    parameter PCIE_TAG_WIDTH        = 8;

    // =====================================================================
    // Common configuration
    // =====================================================================
    // DMA ports per PCIE_ENDPOINT. Total number of dma_ports is PCIE_ENDPOINTS*DMA_PORTS 
    parameter DMA_PORTS = 16;
    // Connected PCIe endpoint type
    // P_TILE, R_TILE
    parameter PCIE_ENDPOINT_TYPE = "P_TILE";
    // Connected PCIe endpoint mode: 0=x16, 1=x8x8, 2=x8
    parameter PCIE_ENDPOINT_MODE = 0;
    // Number of PCIe endpoints
    parameter PCIE_ENDPOINTS     = 1;
    // Number of PCIe clocks per PCIe connector
    parameter PCIE_CLKS          = 2;
    // Number of PCIe connectors
    parameter PCIE_CONS          = 1;
    // Number of PCIe lanes in each PCIe connector
    parameter PCIE_LANES         = 16;
    // Width of CARD/FPGA ID number
    parameter CARD_ID_WIDTH      = 1;
    // Disable PTC module and allows direct connection of the DMA module to
    // the PCIe IP RQ and RC interfaces.
    parameter PTC_DISABLE        = 0;
    // Enable CQ/CC interface for DMA-BAR, condition DMA_PORTS=PCIE_ENDPOINTS
    parameter DMA_BAR_ENABLE     = 0;
    // Enable of XCV IP, for Xilinx only
    parameter XVC_ENABLE         = 0;
    // FPGA device
    // STRATIX10, AGILEX, ULTRASCALE, 7SERIES
    parameter DEVICE             = "AGILEX";

    // AXI META WIDTH
    parameter CQ_MFB_META_W       = sv_pcie_meta_pack::PCIE_CQ_META_WIDTH;
    parameter CC_MFB_META_W       = sv_pcie_meta_pack::PCIE_CC_META_WIDTH;
    parameter RQ_MFB_META_W       = sv_pcie_meta_pack::PCIE_RQ_META_WIDTH;
    parameter RC_MFB_META_W       = sv_pcie_meta_pack::PCIE_RC_META_WIDTH;

    // =====================================================================
    // AXI configuration
    // =====================================================================
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
    parameter RCB                = 1'b0;
    // latency for H-Tile is 18 cycles (20 cycles for safe)
    // latency for P-Tile is 27 cycles (30 cycles for safe)
    // latency for R-Tile is 0 cycles  (FIFO_ENABLE is disabled)
    parameter READY_LATENCY    = (PCIE_ENDPOINT_TYPE == "H_TILE" || PCIE_ENDPOINT_TYPE == "DUMMY") ? 20 : ((PCIE_ENDPOINT_TYPE == "P_TILE") ? 30 : 0);

    parameter PCIE_LEN_MAX      = 128;
    parameter BYTES_LEN_MAX     = PCIE_LEN_MAX*4;

    parameter time PCIE_SYSCLK_CLK_PERIOD = 10ns;
    parameter time MI_CLK_PERIOD          = 5ns;
    parameter time DMA_CLK_PERIOD         = 5ns;

    parameter  TRANSACTION_COUNT      = 1000;


    `include "test.sv"

endpackage
`endif
