/*
 * file       : pkg.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: mag seq rx adapter
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef TEST
`define TEST

package test

    `include "uvm_macros.svh";
    import uvm_pkg::*;

    parameter CLK_PERIOD   = 4ns;
    parameter REGIONS      = 2;
    parameter REGION_SIZE  = 8;
    parameter SEGMENTS     = REGIONS * REGION_SIZE;

	`include "base.sv";
endpackage

`endif

