// pkg.sv: Test package
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
// SPDX-License-Identifier: BSD-3-Clause

`ifndef PACKET_DELAYER_TEST_SV
`define PACKET_DELAYER_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    // ========================================================================
    // DUT generics (overridden by ver_settings.py through multi_ver; keep the
    // "parameter NAME = value;" form on one line, multi_ver rewrites it by sed)
    // ========================================================================
    parameter REGIONS             = 2;
    parameter REGION_SIZE         = 8;
    parameter BLOCK_SIZE          = 8;
    parameter ITEM_WIDTH          = 8;
    parameter META_WIDTH          = 16;
    parameter TS_WIDTH            = 16;
    // 0 = interval (ns from the previous packet), 1 = absolute (ns from the epoch)
    parameter TS_FORMAT           = 1;
    parameter FIFO_DEPTH          = 2048;
    parameter FIFO_AF_OFFSET      = 1000;
    parameter FIFO_AE_OFFSET      = 1000;

    // RX MFB metadata = {META, TS}
    parameter EXTENDED_META_WIDTH = META_WIDTH+TS_WIDTH;

    // ========================================================================
    // Clock and reset
    // ========================================================================
    // Full clock period. CURRENT_TIME increments by 1 per clock, so one
    // timestamp unit = one clock period.
    parameter CLK_PERIOD = 8ns;
    parameter RESET_CLKS = 10;

    // ========================================================================
    // Default stimulus (test::delay_test)
    // ========================================================================
    // Frame size in items (one region holds REGION_SIZE*BLOCK_SIZE items)
    parameter FRAME_SIZE_MIN   = 8;
    parameter FRAME_SIZE_MAX   = REGION_SIZE * BLOCK_SIZE;
    // Number of packets per run
    parameter PACKET_COUNT_MIN = 1000;
    parameter PACKET_COUNT_MAX = 1300;
    // Timestamp step range in clock periods (TS_FORMAT = 0: the timestamp
    // itself, TS_FORMAT = 1: difference of consecutive timestamps)
    parameter TS_MIN           = 4;
    parameter TS_MAX           = 14;
    // Sanity bound of the absolute timestamp (TS_FORMAT = 1)
    parameter TS_ABS_MAX       = (1 << (TS_WIDTH-1)) - 1;

    // ========================================================================
    // Reference model calibration (in clock periods)
    // ========================================================================
    // PIPE_LAT : timestamp comparison -> TX monitor
    // ARRIV_LAT: RX SOF -> head of the TX FIFO (the model adds PIPE_LAT on top)
    // GAP_TIME : gap between the previous EOF and the next SOF (TS_FORMAT = 1)
    parameter PIPE_LAT  = 0;
    parameter ARRIV_LAT = 8;
    parameter GAP_TIME  = 0;

    // ========================================================================
    // Drain after the stimulus: poll every DRAIN_TICK until every packet has
    // been received by the model and matched by both comparers
    // ========================================================================
    parameter time         DRAIN_TICK        = 1us;
    parameter int unsigned DELAY_DRAIN_TICKS = 1000; // 1 ms

    // ========================================================================
    // test::afull_test - continuous RX flood fills the RX FIFO to FIFO_AFULL
    // (PAUSE_REQUEST rises), then drains to FIFO_AEMPTY (PAUSE_REQUEST falls).
    // Time check is disabled: under overload the release is back-pressure driven.
    // ========================================================================
    parameter int unsigned AFULL_PACKET_COUNT_MIN = 2500;
    parameter int unsigned AFULL_PACKET_COUNT_MAX = 3000;
    parameter int unsigned AFULL_TS_MIN           = 1;
    parameter int unsigned AFULL_TS_MAX           = 10;
    parameter int unsigned AFULL_DRAIN_TICKS      = 8000;      // 8 ms
    parameter time         AFULL_PAUSE_WDT        = 10ms;

    // ========================================================================
    // test::time_reset_test - two traffic phases around TIME_RESET pulses
    // (TS_FORMAT = 1 only)
    // ========================================================================
    parameter int unsigned TIME_RESET_COUNT        = 1;
    parameter int unsigned PHASE_PACKET_COUNT      = 200;
    parameter int unsigned TIME_RESET_PULSE_CLKS   = 2;
    parameter int unsigned TIME_RESET_GAP_CLKS     = 8;
    parameter int unsigned TIME_RESET_DRAIN_TICKS  = 4000; // 4 ms per phase

    // ========================================================================
    // Shared types
    // ========================================================================
    typedef uvm_packet_delayer::env #(
        REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, EXTENDED_META_WIDTH, TS_WIDTH, TS_FORMAT,
        CLK_PERIOD, PIPE_LAT, ARRIV_LAT, GAP_TIME
    ) env_t;

    typedef uvm_packet_delayer::virtual_sequencer #(ITEM_WIDTH, EXTENDED_META_WIDTH) vsqr_t;

    `include "sequence.sv"
    `include "pause_checker.sv"
    `include "test.sv"
    `include "test_afull.sv"
    `include "test_time_reset.sv"

endpackage
`endif
