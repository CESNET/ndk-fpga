/*!
 * \file   test_pkg.sv
 * \brief  Test package
 * \author Daniel Kondys <xkondy00@vutbr.cz>
 * \date   2020
 */
 /*
 * Copyright (C) 2020 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

package test_pkg;

    `include "scoreboard.sv"

    localparam PORT_BASE_CONFIG = 0;

    parameter ADDR_WIDTH = 8;
    parameter DATA_WIDTH = 8;
    parameter META_WIDTH = 8;
    parameter PORTS = 8;
    parameter logic PIPE_OUT[PORTS-1:0] = {0,1,1,0,1,0,0,0};
    parameter ADDR_MASK = 8'b11110000;
    parameter ADDR_BASES = 10;
    parameter logic [ADDR_WIDTH-1:0] ADDR_BASE[ADDR_BASES] = {8'b00000000,8'b00011000,8'b00100000,8'b01000000,8'b01100000,8'b10000000,8'b10100000,8'b11000000,8'b11010000,8'b11100000};
    parameter int PORT_MAPPING[ADDR_BASES] = {0,1,2,3,4,5,6,7,0,0};

    parameter DEVICE = "STRATIX10";

    parameter TRANSACTION_COUNT = 1000;

    parameter CLK_PERIOD = 10ns;
    parameter RESET_TIME = 10*CLK_PERIOD;

endpackage
