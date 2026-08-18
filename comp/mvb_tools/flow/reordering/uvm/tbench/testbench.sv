// testbench.sv: Testbench
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
// SPDX-License-Identifier: BSD-3-Clause

import uvm_pkg::*;
`include "uvm_macros.svh"
import test::*;

module testbench;

    typedef test::test_base #(
        .ITEMS (ITEMS),
        .ITEM_WIDTH (ITEM_WIDTH),
        .REORDERING_EN (REORDERING_EN)
    )test_base;

    // ---------------- //
    // Clock definition //
    // ---------------- //

    logic CLK = 0;
    logic RST_INIT = 1'b1;

    always begin
        #(CLK_PERIOD) CLK = ~CLK;
    end

    // ---------- //
    // Interfaces //
    // ---------- //

    reset_if reset (CLK);
    pullup(reset.RESET);

    mvb_if #(
        .ITEMS      (ITEMS),
        .ITEM_WIDTH (ITEM_WIDTH + $clog2(ITEMS))
    ) mvb_rx(CLK);


    mvb_if #(
        .ITEMS      (ITEMS),
        .ITEM_WIDTH (ITEM_WIDTH)
    ) mvb_tx(CLK);

    // ----- //
    // Tests //
    // ----- //


    // Start of tests
    initial begin
        uvm_root m_root;

        // ---------------------- //
        // Database configuration //
        // ---------------------- //

        uvm_config_db #(virtual reset_if)::set(null, "", "vif_reset", reset);

        uvm_config_db #(virtual mvb_if #(
            .ITEMS      (ITEMS),
            .ITEM_WIDTH (ITEM_WIDTH + $clog2(ITEMS))
        ))::set(null, "", "vif_rx_mvb", mvb_rx);

        uvm_config_db #(virtual mvb_if #(
            .ITEMS      (ITEMS),
            .ITEM_WIDTH (ITEM_WIDTH)
        ))::set(null, "", "vif_tx_mvb", mvb_tx);

        m_root = uvm_root::get();
        m_root.finish_on_completion = 0;
        m_root.set_report_id_action_hier("ILLEGALNAME", UVM_NO_ACTION);

        uvm_config_db#(int)            ::set(null, "", "recording_detail", 0);
        uvm_config_db#(uvm_bitstream_t)::set(null, "", "recording_detail", 0);

        run_test();
        $stop(2);
    end

    // --- //
    // dut //
    // --- //

    dut #(
        .ITEMS       (ITEMS),
        .ITEM_WIDTH   (ITEM_WIDTH),
        .OUT_REG_EN    (OUT_REG_EN),
        .REORDERING_EN    (REORDERING_EN)
    )
    DUT_U
    (
        .CLK    (CLK),
        .RST    (reset.RESET == 1'b1 ? 1'b1 : 1'b0),
        .mvb_rx (mvb_rx),
        .mvb_tx (mvb_tx)
    );

    // -------- //
    // Property //
    // -------- //

    mvb_reordering_property #(
        .ITEMS       (ITEMS),
        .ITEM_WIDTH   (ITEM_WIDTH)
    )
    PROPERTY_CHECK (
        .RESET  (reset.RESET == 1'b1 ? 1'b1 : 1'b0),
        .mvb_rx (mvb_rx),
        .mvb_tx (mvb_tx)
    );


endmodule
