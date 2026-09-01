//-- pkg.sv: Test package
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef PCIE_TRANSACTION_CTRL_TEST_SV
`define PCIE_TRANSACTION_CTRL_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    // Number of DMA ports per one PTC, possible values: 1, 2, 4.
    parameter DMA_PORTS             = 2;

    parameter MVB_UP_ITEMS          = 2;
    parameter MFB_UP_REGIONS        = 2;
    parameter MFB_UP_REG_SIZE       = 1;
    parameter MFB_UP_BLOCK_SIZE     = 8;

    parameter DMA_MVB_UP_ITEMS      = 2;
    parameter DMA_MFB_UP_REGIONS    = MFB_UP_REGIONS;

    parameter MVB_DOWN_ITEMS        = 2;
    parameter MFB_DOWN_REGIONS      = 2;
    parameter MFB_DOWN_REG_SIZE     = 1;
    parameter MFB_DOWN_BLOCK_SIZE   = 8;

    parameter DMA_MVB_DOWN_ITEMS    = 2;
    parameter DMA_MFB_DOWN_REGIONS  = MFB_DOWN_REGIONS;

    parameter PCIE_PREFIX_WIDTH     = 32;
    parameter PCIE_TAG_WIDTH        = 8;

    parameter PCIE_STRADDLING       = 1;
    // Only needed for setting MFB FIFO sizes
    parameter MPS                   = 512/4;
    // Only needed when DMA_PORTS>1 for setting MFB FIFO sizes
    parameter MRRS                  = 512/4;
    // Read completion boundary status ('0' = RCB is 64B, '1' = RCB is 128B)
    parameter RCB_SIZE              = 1'b0;

    parameter UP_ASFIFO_ITEMS       = 512;
    parameter DOWN_ASFIFO_ITEMS     = 512;
    parameter DOWN_FIFO_ITEMS       = 512;

    parameter DEVICE                = "STRATIX10"; // "VIRTEX6", "7SERIES", "ULTRASCALE", "STRATIX10"
    // Connected PCIe endpoint type ("H_TILE" or "P_TILE" or "R_TILE") (only relevant on Intel FPGAs)
    parameter ENDPOINT_TYPE         = "P_TILE";
    // PCIE header is in MVB data only if ENDPOINT is P_TILE and DEVICE is STRATIX10 or DEVICE is Agilex

    // VERIFICATION PARAMETERS
    parameter CLK_PERIOD                = 2.22222222ns;
    parameter CLK_DMA_PERIOD            = 5ns;
    // MIN FRAME SIZE
    parameter MIN_READ_REQ_SIZE         = 1;
    parameter MIN_WRITE_REQ_SIZE        = 1;
    // DST RDY PROBABILITY
    parameter DOWN_MVB_DST_RDY_PROB_MIN = 0;
    parameter DOWN_MVB_DST_RDY_PROB_MAX = 100;
    parameter DOWN_MFB_DST_RDY_PROB_MIN = 0;
    parameter DOWN_MFB_DST_RDY_PROB_MAX = 100;
    parameter RQ_MFB_DST_RDY_PROB_MIN   = 0;
    parameter RQ_MFB_DST_RDY_PROB_MAX   = 100;

    `include "test.sv"
    //TODO: ADD test slow
    //`include "test_slow_dma_down.sv"
endpackage
`endif
