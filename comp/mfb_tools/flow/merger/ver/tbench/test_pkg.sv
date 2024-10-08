/*!
 * \file test_pkg.sv
 * \brief Test Package
 * \author Jakub Cabal <cabal@cesnet.cz>
 * \date 2018
 */
 /*
 * Copyright (C) 2018 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

package test_pkg;

    import math_pkg::*;
    import sv_common_pkg::*; // SystemVerilog Boolean

    // DUT parameters
    parameter MERGER_INPUTS   = 2;

    parameter MVB_ITEMS       = 2;
    parameter MVB_ITEM_WIDTH  = 16;

    parameter MFB_REGIONS     = 2;
    parameter MFB_REG_SIZE    = 1;
    parameter MFB_BLOCK_SIZE  = 4;
    parameter MFB_ITEM_WIDTH  = 4;
    parameter MFB_META_WIDTH  = 1;

    parameter INPUT_FIFO_SIZE = 8;
    // THIS IS DECLARED AS 'DOWNTO' BUT SYSTEMVERILOG CREATES IT AS 'TO', WHICH MEANS THERE HAS TO BE A DUT WRAPPER TO CONVERT IT
    // Fixed in ModelSim-SE 2020.4
    parameter bool RX_PAYLOAD_EN[MERGER_INPUTS-1:0] = '{MERGER_INPUTS{TRUE}};
    parameter IN_PIPE_EN      = FALSE;
    parameter OUT_PIPE_EN     = TRUE;
    parameter DEVICE          = "ULTRASCALE";

    // Generator parameters
    parameter FRAME_SIZE_MAX = MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*3; // size is in MFB items
    parameter FRAME_SIZE_MIN = 1; // size is in MFB items
    parameter TRANSACTION_COUNT = 10000;

    parameter int unsigned RX_MVB_SRC_RDY_FALL_CHANCE  [] = {10,20}; // [%]
    parameter int unsigned RX_MVB_SRC_RDY_FALL_TIME_MAX[] = {10,20}; // [CLK ticks]
    parameter int unsigned RX_MFB_SRC_RDY_FALL_CHANCE  [] = {30,20}; // [%]
    parameter int unsigned RX_MFB_SRC_RDY_FALL_TIME_MAX[] = {20,10}; // [CLK ticks]

    parameter TX_MVB_DST_RDY_FALL_CHANCE    = 20; // [%]
    parameter TX_MVB_DST_RDY_FALL_TIME_MAX  = 20; // [CLK ticks]
    parameter TX_MFB_DST_RDY_FALL_CHANCE    = 10; // [%]
    parameter TX_MFB_DST_RDY_FALL_TIME_MAX  = 10; // [CLK ticks]

    // Test parameters
    parameter FULL_PRINT = FALSE;

    // Clock and reset parameters
    parameter CLK_PERIOD = 5ns;
    parameter RESET_TIME = 10*CLK_PERIOD;

    `include "custom_trans.sv"
    `include "scoreboard.sv"
    `include "custom_trans_gen.sv"

endpackage
