// test_pkg.sv
// Copyright (C) 2019 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

package test_pkg;

    import math_pkg::*;
    import sv_common_pkg::TRUE, sv_common_pkg::FALSE;

    // Parameters for generic
    // ======================
    // RX MII configuration, allows you to set the required input data width
    // according to the selected Ethernet standard.
    parameter MII_DATA_WIDTH  = 1024;
    parameter MII_LANE_WIDTH  = 64;
    parameter RX_ITEM_WIDTH   = 8;

    // By default the (TX-AUTO) parameters are calculated automatically from MII_DATA_WIDTH.
    parameter TXA_REGIONS     = math_pkg::max(MII_DATA_WIDTH/512,1);
    parameter TXA_BLOCK_SIZE  = 8;
    parameter TXA_ITEM_WIDTH  = 8;
    parameter TXA_REGION_SIZE = (MII_DATA_WIDTH/TXA_REGIONS)/(TXA_BLOCK_SIZE*TXA_ITEM_WIDTH);

    // TX MFB configuration, by default the same as RX. Useful, for example,
    // for enlargement data width from 128b (RX) to 512b (TX).
    parameter TX_REGIONS      = TXA_REGIONS;
    parameter TX_REGION_SIZE  = TXA_REGION_SIZE;
    parameter TX_BLOCK_SIZE   = TXA_BLOCK_SIZE;
    parameter TX_ITEM_WIDTH   = TXA_ITEM_WIDTH;

    parameter RESIZE_BUFFER   = 0;
    parameter METADATA_WIDTH  = 102;

    parameter CRC_CHECK_EN    = 0;
    parameter MAC_CHECK_EN    = 0;
    parameter MAC_COUNT_MAX   = 16;
    parameter TIMESTAMP_EN    = FALSE;
    parameter INBANDFCS       = 0;

    // Parameters for MI32 configuration
    parameter FRAME_LEN_MAX = 501;
    parameter FRAME_LEN_MIN = 67;
    parameter MAC_COUNT = 10;
    parameter MAC_CHECK_MODE = 3;

    // Generator parameters
    parameter FRAME_SIZE_MAX    = 4096;
    parameter FRAME_SIZE_MIN    = 256;
    parameter TRANSACTION_COUNT = 4000;

    parameter RX_CLK_PERIOD = 5.1ns;
    parameter TX_CLK_PERIOD = 5ns;
    parameter MI_CLK_PERIOD = 7ns;
    parameter RESET_TIME    = 10*MI_CLK_PERIOD;

    // -- RFC2819 Counter addresses
    //Use extended or base address space
    //  * 1 = enabled
    //  * 0 = disabled (use output address space command)
    parameter USE_RFC2819_EXTENDED = 1;
    // Base RFC2819 address
    int unsigned RFC2819_BASE_ADDRESS = 32'h100;
    // Counter addresses - format {non-switched address, switched address
    int unsigned RFC2819_ADDRESSES[][] = '{
        {32'h00,RFC2819_BASE_ADDRESS + 32'h00}, //CRC Error counters (low)
        {32'h04,RFC2819_BASE_ADDRESS + 32'h04}, //MTU error counters (low)
        {32'h08,RFC2819_BASE_ADDRESS + 32'h08}, //Minimal TU error (low)
        {32'h0C,RFC2819_BASE_ADDRESS + 32'h0C}, //Received broadcast frames (low)
        {32'h10,RFC2819_BASE_ADDRESS + 32'h10}, //Received multicast frames (low)
        {32'h14,RFC2819_BASE_ADDRESS + 32'h14}, //Received fragment frames (low)
        {32'h18,RFC2819_BASE_ADDRESS + 32'h18}, //Received jabber frames (low)
        {32'h1C,RFC2819_BASE_ADDRESS + 32'h1C}, //Number of transfered octets(low)
        {32'h20,RFC2819_BASE_ADDRESS + 32'h20}, //Frames - length 64 (low)
        {32'h24,RFC2819_BASE_ADDRESS + 32'h24}, //Frames - length 65 to 127 (low)
        {32'h28,RFC2819_BASE_ADDRESS + 32'h28}, //Frames - length 128 to 255 (low)
        {32'h2C,RFC2819_BASE_ADDRESS + 32'h2C}, //Frames - length 256 to 511 (low)
        {32'h30,RFC2819_BASE_ADDRESS + 32'h30}, //Frames - length 512 to 1023 (low)
        {32'h34,RFC2819_BASE_ADDRESS + 32'h34}, //Frames - length 1024 to 1518 (low)

        {32'h38,RFC2819_BASE_ADDRESS + 32'h38}, //CRC Error counters (high)
        {32'h3C,RFC2819_BASE_ADDRESS + 32'h3C}, //MTU error counters (high)
        {32'h40,RFC2819_BASE_ADDRESS + 32'h40}, //Minimal TU error (high)
        {32'h44,RFC2819_BASE_ADDRESS + 32'h44}, //Received broadcast frames (high)
        {32'h48,RFC2819_BASE_ADDRESS + 32'h48}, //Received multicast frames (high)
        {32'h4C,RFC2819_BASE_ADDRESS + 32'h4C}, //Received fragment frames (high)
        {32'h50,RFC2819_BASE_ADDRESS + 32'h50}, //Received jabber frames (high)
        {32'h54,RFC2819_BASE_ADDRESS + 32'h54}, //Number of transfered octets(high)
        {32'h58,RFC2819_BASE_ADDRESS + 32'h58}, //Frames - length 64 (high)
        {32'h5C,RFC2819_BASE_ADDRESS + 32'h5C}, //Frames - length 65 to 127 (high)
        {32'h60,RFC2819_BASE_ADDRESS + 32'h60}, //Frames - length 128 to 255 (high)
        {32'h64,RFC2819_BASE_ADDRESS + 32'h64}, //Frames - length 256 to 511 (high)
        {32'h68,RFC2819_BASE_ADDRESS + 32'h68}, //Frames - length 512 to 1023 (high)
        {32'h6C,RFC2819_BASE_ADDRESS + 32'h6C}, //Frames - length 1024 to 1518 (high)

        // Extension of the address space with new counters
        {32'h70,RFC2819_BASE_ADDRESS + 32'h70}, //Frames - length over 1518 (low)
        {32'h74,RFC2819_BASE_ADDRESS + 32'h74}, //Frames - length over 1518 (high)
        {32'h78,RFC2819_BASE_ADDRESS + 32'h78}, //Frames - length below 64 (low)
        {32'h7C,RFC2819_BASE_ADDRESS + 32'h7C}  //Frames - length below 64 (high)
    };

    `include "my_trans.sv"
    `include "scoreboard.sv"

endpackage
