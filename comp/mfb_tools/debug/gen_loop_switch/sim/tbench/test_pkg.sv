/*
 * file: test_pkg.sv
 * brief: Test Package
 * author: Jan Kubalek <kubalek@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 * date: 2020
 */

package test_pkg;

    import math_pkg::*;
    `include "scoreboard.sv"

    parameter CLK_PERIOD    = 10ns;
    parameter MI_CLK_PERIOD = 10ns;
    parameter RESET_TIME    = 10*CLK_PERIOD;

    parameter FRAME_SIZE_MAX    = 512;
    parameter FRAME_SIZE_MIN    = 60;
    parameter TRANSACTION_COUNT = 100;
    parameter VERBOSE_LEVEL     = 0;

    parameter REGIONS           = 2;
    parameter REGION_SIZE       = 16;
    parameter BLOCK_SIZE        = 16;
    parameter ITEM_WIDTH        = 1;
    parameter PKT_MTU           = 2**8;
    parameter RX_DMA_CHANNELS   = 16;
    parameter TX_DMA_CHANNELS   = 16;
    parameter NPP_HDR_SIZE      = 4;
    parameter HDR_META_WIDTH    = 4;
    parameter RX_HDR_INS_EN     = FALSE;
    parameter SAME_CLK          = (CLK_PERIOD==MI_CLK_PERIOD);
    parameter MI_PIPE_EN        = TRUE;
    parameter DEVICE            = "STRATIX10";

endpackage
