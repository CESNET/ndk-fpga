// testbench.sv: Testbench
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

import uvm_pkg::*;
`include "uvm_macros.svh"
import test::*;

module testbench;

    // ---------------- //
    // Clock definition //
    // ---------------- //

    logic CLK = 0;

    always #(CLK_PERIOD) CLK = ~CLK;

    // ---------- //
    // Interfaces //
    // ---------- //

    reset_if                                                                       reset (CLK);
    mfb_if #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH+1+LEN_WIDTH) mfb_rx(CLK);
    mfb_if #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)             mfb_tx(CLK);

    // ----- //
    // Tests //
    // ----- //

    typedef test::test_base  #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, LEN_WIDTH) test_base;
    typedef test::test_speed #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, LEN_WIDTH) test_speed;

    // Start of tests
    initial begin
        uvm_root m_root;

        // ---------------------- //
        // Database configuration //
        // ---------------------- //

        uvm_config_db #(virtual reset_if)                                                                      ::set(null, "", "vif_reset", reset);
        uvm_config_db #(virtual mfb_if #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH+1+LEN_WIDTH))::set(null, "", "vif_rx_mfb", mfb_rx);
        uvm_config_db #(virtual mfb_if #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))            ::set(null, "", "vif_tx_mfb", mfb_tx);

        m_root = uvm_root::get();
        m_root.finish_on_completion = 0;
        m_root.set_report_id_action_hier("ILLEGALNAME", UVM_NO_ACTION);

        uvm_config_db#(int)            ::set(null, "", "recording_detail", 0);
        uvm_config_db#(uvm_bitstream_t)::set(null, "", "recording_detail", 0);

        run_test();
        $stop(2);
    end

    // --- //
    // DUT //
    // --- //

    DUT #(
        .REGIONS     (REGIONS),
        .REGION_SIZE (REGION_SIZE),
        .BLOCK_SIZE  (BLOCK_SIZE),
        .ITEM_WIDTH  (ITEM_WIDTH),
        .META_WIDTH  (META_WIDTH),
        .LEN_WIDTH   (LEN_WIDTH),
        .DEVICE      (DEVICE)
    )
    DUT_U (
        .CLK    (CLK),
        .RST    (reset.RESET),
        .mfb_rx (mfb_rx),
        .mfb_tx (mfb_tx)
    );

    // -------- //
    // Property //
    // -------- //

    mfb_frame_trimmer_property #(
        .REGIONS     (REGIONS),
        .REGION_SIZE (REGION_SIZE),
        .BLOCK_SIZE  (BLOCK_SIZE),
        .ITEM_WIDTH  (ITEM_WIDTH),
        .META_WIDTH  (META_WIDTH),
        .LEN_WIDTH   (LEN_WIDTH)
    )
    PROPERTY_CHECK (
        .RESET  (reset.RESET),
        .mfb_rx (mfb_rx),
        .mfb_tx (mfb_tx)
    );

endmodule
