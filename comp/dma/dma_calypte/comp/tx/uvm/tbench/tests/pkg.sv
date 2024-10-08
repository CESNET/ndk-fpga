// pkg.sv: package with all tests
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Daniel Kriz <danielkriz@cesnet.cz>
//            Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

`ifndef TX_DMA_CALYPTE_TEST_SV
`define TX_DMA_CALYPTE_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    parameter DEVICE                  = "ULTRASCALE";

    parameter MI_WIDTH                = 32;

    parameter USR_MFB_REGIONS         = 1;
    parameter USR_MFB_REGION_SIZE     = 8;
    parameter USR_MFB_BLOCK_SIZE      = 8;
    parameter USR_MFB_ITEM_WIDTH      = 8;

    parameter PCIE_CQ_MFB_REGIONS     = 2;
    parameter PCIE_CQ_MFB_REGION_SIZE = 1;
    parameter PCIE_CQ_MFB_BLOCK_SIZE  = 8;
    parameter PCIE_CQ_MFB_ITEM_WIDTH  = 32;

    parameter CHANNELS                = 4;
    parameter CNTRS_WIDTH             = 64;
    parameter HDR_META_WIDTH          = 24;

    parameter DATA_POINTER_WIDTH      = 13;
    parameter DMA_HDR_POINTER_WIDTH   = 10;

    // Max size bytes of DMA frame
    parameter PKT_SIZE_MAX            = 2**12;
    // Parameters that set min and max size of PCIE transaction
    parameter PCIE_LEN_MAX            = 256;

    parameter CLK_PERIOD              = 4ns;

    `include "sequence.sv"
    `include "base.sv"
    `include "speed.sv"

endpackage
`endif
