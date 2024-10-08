/*
 * file       : pkg.sv
 * description: test pkg
 * date       : 2020
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * Copyright (C) 2020 CESNET
 * SPDX-License-Identifier: BSD-3-Clause
*/

package env;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

     localparam REGIONS = 2;
     localparam ITEM_WIDTH = 32;
     localparam MFB_META_RX_WIDTH = 32+128;
     localparam MFB_META_TX_WIDTH = 3+32+128;

    `include "sequencer.sv"
    `include "scoreboard.sv"
    `include "sequence.sv"
    `include "env.sv"
endpackage
