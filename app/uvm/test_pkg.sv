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

    parameter time CLK_PERIOD           = 10ns;

    parameter int unsigned ETH_PORTS            = 2;
    parameter int unsigned ETH_STREAMS          = 2;
    parameter int unsigned ETH_CHANNELS         = 4;
    parameter int unsigned ETH_PKT_MTU          = 2**12;
    parameter int unsigned ETH_RX_HDR_WIDTH     = 102;
    parameter int unsigned ETH_TX_HDR_WIDTH     = 25;
    parameter int unsigned PCIE_ENDPOINTS       = 2;
    parameter int unsigned DMA_STREAMS          = 2;
    parameter int unsigned DMA_RX_CHANNELS      = 8; //10;
    parameter int unsigned DMA_TX_CHANNELS      = 8;
    parameter int unsigned DMA_HDR_META_WIDTH   = 12;
    parameter int unsigned DMA_PKT_MTU          = 2**12;
    parameter int unsigned REGIONS              = 4;
    parameter int unsigned MFB_REG_SIZE         = 8;
    parameter int unsigned MFB_BLOCK_SIZE       = 8;
    parameter int unsigned MFB_ITEM_WIDTH       = 8;
    parameter int unsigned MEM_PORTS            = 1;
    parameter int unsigned MEM_ADDR_WIDTH       = 26;
    parameter int unsigned MEM_BURST_WIDTH      = 7;
    parameter int unsigned MEM_DATA_WIDTH       = 512;
    parameter int unsigned MEM_REFR_PERIOD_WIDTH = 32;
    parameter logic [MEM_REFR_PERIOD_WIDTH-1:0] MEM_DEF_REFR_PERIOD[MEM_PORTS-1:0]  =  '{MEM_PORTS{128}};
    parameter int unsigned MI_DATA_WIDTH        = 32;
    parameter int unsigned MI_ADDR_WIDTH        = 32;
    parameter int unsigned RESET_WIDTH          = 4;
    parameter string BOARD                = "400G1";
    parameter string DEVICE               = "ULTRASCALE";

endpackage
