//-- pkg.sv: test packages
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef NETWORK_MOD_TEST_SV
`define NETWORK_MOD_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    parameter ETH_CORE_ARCH     = "F_TILE";
    parameter ETH_PORTS         = 2;
    parameter int unsigned ETH_PORT_SPEED[ETH_PORTS-1:0]  = '{ETH_PORTS{400}};
    parameter int unsigned ETH_PORT_CHAN[ETH_PORTS-1:0]   = '{ETH_PORTS{1}};
    parameter int unsigned EHIP_PORT_TYPE[ETH_PORTS-1:0]  = '{ETH_PORTS{0}};
    parameter int unsigned ETH_PORT_RX_MTU[ETH_PORTS-1:0] = '{ETH_PORTS{16383}};
    parameter int unsigned ETH_PORT_TX_MTU[ETH_PORTS-1:0] = '{ETH_PORTS{16383}};
    parameter LANES             = 8;
    parameter QSFP_PORTS        = 2;
    parameter QSFP_I2C_PORTS    = 1;
    parameter QSFP_I2C_TRISTATE = 1'b1;
    parameter REGIONS           = 4;
    parameter REGION_SIZE       = 8;
    parameter BLOCK_SIZE        = 8;
    parameter ITEM_WIDTH        = 8;
    parameter MI_DATA_WIDTH     = 32;
    parameter MI_ADDR_WIDTH     = 32;

    /*/ TYTO KONSTANTY JSOU K NICEMU UPOZORNIT KUBU */
    parameter MI_DATA_WIDTH_PHY = 32;
    parameter MI_ADDR_WIDTH_PHY = 32;


    parameter LANE_RX_POLARITY  = 0; //'{ETH_PORTS*LANES{1'b0}};
    parameter LANE_TX_POLARITY  = 0; //'{ETH_PORTS*LANES{1'b0}};
    parameter RESET_WIDTH       = 8;
    parameter DEVICE            = "AGILEX";
    parameter BOARD             = "N6010";

    parameter ETH_TX_HDR_WIDTH = 16+8+1;
    parameter ETH_RX_HDR_WIDTH = 64+1+4+1+1+1+1+1+1+1+1+1+8+16;

    parameter time CLK_USR_PERIOD    = 4ns;
    parameter time CLK_ETH_PERIOD[ETH_PORTS] = '{ETH_PORTS{4ns}};
    parameter time CLK_MI_PERIOD     = 4ns;
    parameter time CLK_MI_PHY_PERIOD = 4ns;
    parameter time CLK_MI_PMD_PERIOD = 4ns;
    parameter time CLK_TSU_PERIOD    = 4ns;

    parameter int unsigned PACKET_SIZE_MIN = 64;
    parameter int unsigned PACKET_SIZE_MAX = 16384;

    `include "base.sv"
    `include "speed.sv"

endpackage

`endif
