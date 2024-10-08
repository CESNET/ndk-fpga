/*!
 * \file test_pkg.sv
 * \brief Test Package
 * \author Daniel Kriz <xkrizd01@vutbr.cz>
 * \date 2020
 */
 /*
 * Copyright (C) 2020 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

package test_pkg;

    parameter MVB_ITEMS = 8;
    parameter MFB_REGIONS = 2;
    parameter MFB_REGION_SIZE = 1;
    parameter MFB_BLOCK_SIZE = 8;
    parameter MFB_ITEM_WIDTH = 32;

    parameter MFB_META_WIDTH = 2;
    parameter MFB_META_ALIGNMENT = 1;

    parameter EXTRACT_MODE = 1;

    parameter VERBOSE = 0;

    parameter OUT_MVB_PIPE_EN = 0;
    parameter OUT_MFB_PIPE_EN = 0;

    parameter FRAME_SIZE_MAX = 512;
    parameter FRAME_SIZE_MIN = 60;
    parameter TRANSACTION_COUNT = 2000;

    parameter CLK_PERIOD = 10ns;
    parameter RESET_TIME = 10*CLK_PERIOD;

    `include "scoreboard.sv"
endpackage
