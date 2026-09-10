/*!
 * \file test_pkg.sv
 * \brief Test Package
 * \author Jakub Cabal <xcabal05@stud.feec.vutbr.cz>
 * \date 2017
 */
 /*
 * Copyright (C) 2017 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */



package test_pkg;

    import math_pkg::*;
    import sv_common_pkg::*; // SystemVerilog Boolean
    `include "scoreboard.sv"

    // DUT parameters
    // Number of independent input MFB interfaces (N inputs merged to one output).
    parameter MERGER_INPUTS = 5;

    parameter MFB_REGIONS     = 4;
    parameter MFB_REGION_SIZE = 1;
    parameter MFB_BLOCK_SIZE  = 8;
    parameter MFB_ITEM_WIDTH  = 32;
    parameter MFB_META_WIDTH  = 8;

    // Maximum amount of clock periods with destination ready before the Merger
    // tries to switch to another input (starvation prevention). MASKING_EN is
    // left at the entity default (TRUE) and is not swept here.
    parameter CNT_MAX = 64;

    // Generator parameters
    parameter FRAME_SIZE_MAX    = 512;
    parameter FRAME_SIZE_MIN    = 60;
    parameter TRANSACTION_COUNT = 10000;

    // Per-input source-ready gap randomization (drives back-to-back contention
    // and exercises the round-robin + CNT_MAX arbitration). Declared unsized so
    // the ver_settings.py sweep can substitute an initializer of matching length
    // for each MERGER_INPUTS value (see flow/merger for the same convention).
    parameter int unsigned RX_MFB_SRC_RDY_FALL_CHANCE  [] = {30, 20, 50, 10, 40}; // [%]
    parameter int unsigned RX_MFB_SRC_RDY_FALL_TIME_MAX[] = {20, 10, 20, 10, 20}; // [CLK ticks]

    // Output (TX) destination-ready backpressure.
    parameter TX_MFB_DST_RDY_FALL_CHANCE    = 10; // [%]
    parameter TX_MFB_DST_RDY_FALL_TIME_MAX  = 10; // [CLK ticks]

    // Clock and reset parameters
    parameter CLK_PERIOD = 10ns;
    parameter RESET_TIME = 10*CLK_PERIOD;

endpackage
