/*
 * file       : pkg.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: pma pkg
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef PMA_PKG
`define PMA_PKG

package uvm_pma;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    parameter C_HDR   = 2'b01; // GBASR-R control block header
    parameter D_HDR   = 2'b10; // GBASR-R data block header

    parameter BT_C_C  = 8'h1E; // 8 controls (idles) in a block   0001_1110
    parameter BT_S_D  = 8'h78; // start + 3 data + 4 data         0111_1000
    parameter BT_O_S  = 8'h66; // ordered set + start + 3 data
    parameter BT_C_S  = 8'h33; // 4 controls + start + 3 data     0011_0011
    parameter BT_T_C  = 8'h87; // terminate + 7 controls          1000_0111
    parameter BT_D1_C = 8'h99; // 1 data + terminate + 6 controls 1001_1001
    parameter BT_D2_C = 8'haa; // 2 data + terminate + 5 controls 1010_1010
    parameter BT_D3_C = 8'hb4; // 3 data + terminate + 4 controls 1011_0100
    parameter BT_D4_C = 8'hcc; // 4 data + terminate + 3 controls 1100_1100
    parameter BT_D5_C = 8'hd2; // 5 data + terminate + 2 controls 1101_0010
    parameter BT_D6_C = 8'he1; // 6 data + terminate + 1 control  1110_0001
    parameter BT_D7_T = 8'hff; // 7 data + terminate              1111_1111
    parameter UNKNOWN = 8'h20; // UNKNOWM HEADER

    `include "config.sv"
    `include "sequence_item.sv"
    `include "sequencer.sv"
    `include "driver.sv"
    `include "monitor.sv"
    `include "agent.sv"

endpackage

`endif
