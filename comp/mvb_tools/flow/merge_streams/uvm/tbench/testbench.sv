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

    reset_if                            reset             (CLK);
    mvb_if #(
        .ITEMS      (MVB_ITEMS),
        .ITEM_WIDTH (MVB_ITEM_WIDTH)
    ) mvb_rx[RX_STREAMS](CLK);
    mvb_if #(
        .ITEMS      (MVB_ITEMS),
        .ITEM_WIDTH (MVB_ITEM_WIDTH)
    ) mvb_tx            (CLK);

    // ----- //
    // Tests //
    // ----- //

    typedef test::test_base #(
        .MVB_ITEMS      (MVB_ITEMS),
        .MVB_ITEM_WIDTH (MVB_ITEM_WIDTH),
        .RX_STREAMS     (RX_STREAMS)
    ) test_base;
    typedef test::test_speed #(
        .MVB_ITEMS      (MVB_ITEMS),
        .MVB_ITEM_WIDTH (MVB_ITEM_WIDTH),
        .RX_STREAMS     (RX_STREAMS)
    ) test_speed;

    // Start of tests
    initial begin
        uvm_root m_root;

        // ---------------------- //
        // Database configuration //
        // ---------------------- //

        automatic virtual mvb_if #(
            .ITEMS      (MVB_ITEMS),
            .ITEM_WIDTH (MVB_ITEM_WIDTH)
        ) v_mvb_rx[RX_STREAMS] = mvb_rx;

        // Database configuration
        uvm_config_db #(virtual reset_if)::set(null, "", "vif_reset", reset);
        for (int unsigned i = 0; i < RX_STREAMS; i++) begin
            uvm_config_db #(virtual mvb_if #(
                .ITEMS      (MVB_ITEMS),
                .ITEM_WIDTH (MVB_ITEM_WIDTH)
            ))::set(null, "", $sformatf("vif_rx_mvb_%0d", i), v_mvb_rx[i]);
        end
        uvm_config_db #(virtual mvb_if #(
            .ITEMS      (MVB_ITEMS),
            .ITEM_WIDTH (MVB_ITEM_WIDTH)
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
        .MVB_ITEMS       (MVB_ITEMS),
        .MVB_ITEM_WIDTH  (MVB_ITEM_WIDTH),
        .RX_STREAMS      (RX_STREAMS),
        .RX_SHAKEDOWN_EN (RX_SHAKEDOWN_EN),
        .SW_TIMEOUT_W    (SW_TIMEOUT_W),
        .DEVICE          (DEVICE)
    )
    DUT_U (
        .CLK    (CLK),
        .RST    (reset.RESET),
        .mvb_rx (mvb_rx),
        .mvb_tx (mvb_tx)
    );

    // -------- //
    // Property //
    // -------- //

    mvb_merge_streams_property #(
        .MVB_ITEMS      (MVB_ITEMS),
        .MVB_ITEM_WIDTH (MVB_ITEM_WIDTH),
        .RX_STREAMS     (RX_STREAMS)
    )
    PROPERTY_CHECK (
        .RESET  (reset.RESET),
        .mvb_rx (mvb_rx),
        .mvb_tx (mvb_tx)
    );

endmodule
