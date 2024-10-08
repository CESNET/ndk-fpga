// pkg.sv: Test package
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kříž <danielkriz@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


`ifndef TIMESTAMP_LIMITER_TEST_SV
`define TIMESTAMP_LIMITER_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    // //////////////////////
    //  COMPONENT PARAMETERS
    // //////////////////////

    // Number of Regions within a data word, must be power of 2.
    parameter MFB_REGIONS       = 1;
    // Region size (in Blocks).
    parameter MFB_REGION_SIZE   = 8;
    // Block size (in Items), must be 8.
    parameter MFB_BLOCK_SIZE    = 8;
    // Item width (in bits), must be 8.
    parameter MFB_ITEM_WIDTH    = 8;
    // Width of Metadata (in bits).
    parameter MFB_META_WIDTH    = 32;

    // Freq of the CLK signal (in Hz).
    parameter CLK_FREQUENCY     = 200000000;
    // Width of Timestamps (in bits).
    parameter TIMESTAMP_WIDTH   = 48;
    // Format of Timestamps. Options:
    //
    // - ``0`` number of NS between individual packets,
    // - ``1`` number of NS from RESET. WIP, not used yet
    parameter TIMESTAMP_FORMAT  = 1;
    // Number of Items in the Packet Delayer's RX FIFO (the main buffer).
    parameter BUFFER_SIZE       = 2048;
    // The number of Queues (DMA Channels).
    parameter QUEUES            = 2;
    // Maximum size of a packet (in Items).
    parameter PKT_MTU           = 2**11;

    // FPGA device name: ULTRASCALE, STRATIX10, AGILEX, ...
    parameter DEVICE            = "STRATIX10";

    parameter MI_DATA_WIDTH     = 32;
    parameter MI_ADDR_WIDTH     = 32;

    // /////////////////////////
    //  VERIFICATION PARAMETERS
    // /////////////////////////

    // Freq of the CLK period (in ns).
    parameter CLK_PERIOD        = 5ns;

    // Minimum size of a packet (in Items).
    parameter FRAME_SIZE_MIN    = 60;
    // Minimum value of a TS.
    parameter TIMESTAMP_MIN     = 0;
    // Maximum value of a TS. Maximum is 2**TIMESTAMP_WIDTH.
    parameter TIMESTAMP_MAX     = 50;

    // Width of RX Metadata (in bits).
    parameter RX_MFB_META_WIDTH = MFB_META_WIDTH + TIMESTAMP_WIDTH + $clog2(QUEUES);
    // Width of TX Metadata (in bits).
    parameter TX_MFB_META_WIDTH = MFB_META_WIDTH;

    `include "sequence.sv"
    `include "test.sv"
    `include "speed.sv"
endpackage
`endif
