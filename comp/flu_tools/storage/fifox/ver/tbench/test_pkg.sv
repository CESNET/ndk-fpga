/*!
 * \file test_pkg.sv
 * \brief Test Package
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2016
 */
 /*
 * Copyright (C) 2016 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */



package test_pkg;

    import math_pkg::*;


    parameter string DEVICE = "ULTRASCALE";
    parameter DATA_WIDTH = 256;
    parameter SOP_POS_WIDTH = 2;
    parameter ITEMS = 1024;

    parameter EOP_POS_WIDTH = log2(DATA_WIDTH/8);


    parameter TRANSACTION_COUNT = 10000;
    int GENERATOR0_FLU_PACKET_SIZE_MAX = 96;
    int GENERATOR0_FLU_PACKET_SIZE_MIN = 8;


    parameter DRIVER0_DELAYEN_WT         = 1;
    parameter DRIVER0_DELAYDIS_WT        = 50;
    parameter DRIVER0_DELAYLOW           = 0;
    parameter DRIVER0_DELAYHIGH          = 10;
    parameter DRIVER0_INSIDE_DELAYEN_WT  = 1;
    parameter DRIVER0_INSIDE_DELAYDIS_WT = 50;
    parameter DRIVER0_INSIDE_DELAYLOW    = 0;
    parameter DRIVER0_INSIDE_DELAYHIGH   = 10;
    parameter DRIVER0_START_POS_LOW      = 0;
    parameter DRIVER0_START_POS_HIGH     = 2**SOP_POS_WIDTH-1;


    parameter MONITOR0_DELAYEN_WT         = 1;
    parameter MONITOR0_DELAYDIS_WT        = 50;
    parameter MONITOR0_DELAYLOW           = 0;
    parameter MONITOR0_DELAYHIGH          = 10;
    parameter MONITOR0_INSIDE_DELAYEN_WT  = 1;
    parameter MONITOR0_INSIDE_DELAYDIS_WT = 50;
    parameter MONITOR0_INSIDE_DELAYLOW    = 0;
    parameter MONITOR0_INSIDE_DELAYHIGH   = 10;


    parameter CLK_PERIOD = 10ns;
    parameter RESET_TIME = 10*CLK_PERIOD;


    `include "scoreboard.sv"

endpackage
