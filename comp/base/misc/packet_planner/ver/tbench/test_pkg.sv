//-- test_pkg.sv: Test Package.
//-- Copyright (C) 2020 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

package test_pkg;

    import math_pkg::*;
    import sv_common_pkg::*;

    // -- Frequently changed parameters ---------------------------------------------------
    parameter TRANSACTION_COUNT = 1000;
    parameter VERBOSE_LEVEL = 0;
    parameter MAX_NUMBER_OF_PACKETS_TO_BE_REMOVED =10;

    // -- Clocks and resets ---------------------------------------------------------------
    parameter CLK_PERIOD = 10ns;
    parameter RESET_TIME = 10 * CLK_PERIOD;

    // -- DUT parameters ------------------------------------------------------------------
    parameter NUMBER_OF_STREAMS   = 5;
    parameter NUMBER_OF_PACKETS   = 4;
    parameter PACKETS_IN_ONE_STEP = NUMBER_OF_PACKETS * NUMBER_OF_STREAMS;      // -- Can be changed to value that is not depend on other parameters.
    parameter META_WIDTH          = 4;

    parameter PACKET_SIZE         = 64;
    parameter SPACE_SIZE          = 2**14;
    parameter GAP_SIZE            = 12;
    parameter MINIMAL_GAP_SIZE    = GAP_SIZE-4;
    parameter ADRESS_ALIGNMENT    = 8;                                          // -- This value must be 2^x.
    parameter FIFO_ITEMS          = 16;
    parameter FIFO_AFULL          = FIFO_ITEMS/2;
    parameter STREAM_OUTPUT_EN    = 1;
    parameter GLOBAL_OUTPUT_EN    = 1;                                          // -- If this parameter is 0 then control of minimal gap between packets are disabled.
    parameter STREAM_OUTPUT_AFULL = 0;
    parameter GLOBAL_OUTPUT_AFULL = 0;

    // -- Constant verification parameters ------------------------------------------------
    parameter LEN                   = log2(PACKET_SIZE+1);
    parameter ADDRES_WIDTH          = log2(SPACE_SIZE);

    parameter RX_ITEM_WIDTH         = META_WIDTH + LEN;

    parameter TX_ITEM_WIDTH         = RX_ITEM_WIDTH + ADDRES_WIDTH;

    parameter TX_GLOBAL_ITEMS       = PACKETS_IN_ONE_STEP;
    parameter TX_GLOBAL_ITEM_WIDTH  = TX_ITEM_WIDTH;

    parameter SPACE_GLB_PTR         = log2(SPACE_SIZE)-log2(ADRESS_ALIGNMENT);

    `include "scoreboard.sv"

endpackage
