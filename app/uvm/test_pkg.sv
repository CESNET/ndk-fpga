/*
 * file       : test_pkg.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: DUT configuration file. This file contains top level generic paramet 
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

package test_pkg;

    parameter CLK_PERIOD           = 10ns;

    parameter ETH_PORTS            = 2;
    parameter ETH_STREAMS          = 2;
    parameter ETH_CHANNELS         = 4;
    parameter ETH_PKT_MTU          = 2**12;
    parameter ETH_RX_HDR_WIDTH     = 102;
    parameter ETH_TX_HDR_WIDTH     = 25;
    parameter PCIE_ENDPOINTS       = 2;
    parameter DMA_STREAMS          = 2;
    parameter DMA_RX_CHANNELS      = 8; //10;
    parameter DMA_TX_CHANNELS      = 8;
    parameter DMA_HDR_META_WIDTH   = 12;
    parameter DMA_PKT_MTU          = 2**12;
    parameter REGIONS              = 4;
    parameter MFB_REG_SIZE         = 8;
    parameter MFB_BLOCK_SIZE       = 8;
    parameter MFB_ITEM_WIDTH       = 8;
    parameter MEM_PORTS            = 1;
    parameter MEM_ADDR_WIDTH       = 26;
    parameter MEM_BURST_WIDTH      = 7;
    parameter MEM_DATA_WIDTH       = 512;
    parameter MEM_REFR_PERIOD_WIDTH = 32;
    parameter logic [MEM_REFR_PERIOD_WIDTH-1:0] MEM_DEF_REFR_PERIOD[MEM_PORTS-1:0]  =  '{MEM_PORTS{128}};
    parameter MI_DATA_WIDTH        = 32;
    parameter MI_ADDR_WIDTH        = 32;
    parameter RESET_WIDTH          = 4;
    parameter BOARD                = "400G1";
    parameter DEVICE               = "ULTRASCALE";

endpackage
