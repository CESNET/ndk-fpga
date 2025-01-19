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

    reset_if                       reset           (CLK);
    mvb_if #(RX_ITEMS, ITEM_WIDTH) mvb_rx          (CLK);
    mvb_if #(1, ITEM_WIDTH)        mvb_tx[TX_ITEMS](CLK);

    // ----- //
    // Tests //
    // ----- //

    typedef test::test_base  #(RX_ITEMS, TX_ITEMS, ITEM_WIDTH) test_base;
    typedef test::test_speed #(RX_ITEMS, TX_ITEMS, ITEM_WIDTH) test_speed;

    // Start of tests
    initial begin
        uvm_root m_root;

        // ---------------------- //
        // Database configuration //
        // ---------------------- //

        automatic virtual mvb_if #(1, ITEM_WIDTH) v_mvb_tx[TX_ITEMS] = mvb_tx;

        uvm_config_db #(virtual reset_if)                      ::set(null, "", "vif_reset",  reset);
        uvm_config_db #(virtual mvb_if #(RX_ITEMS, ITEM_WIDTH))::set(null, "", "vif_rx_mvb", mvb_rx);
        for (int unsigned i = 0; i < TX_ITEMS; i++) begin
            uvm_config_db #(virtual mvb_if #(1, ITEM_WIDTH))::set(null, "", $sformatf("vif_tx_mvb_%0d", i), v_mvb_tx[i]);
        end

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
        .RX_ITEMS     (RX_ITEMS),
        .TX_ITEMS     (TX_ITEMS),
        .ITEM_WIDTH   (ITEM_WIDTH),
        .SHAKE_PORTS  (SHAKE_PORTS),
        .USE_MUX_IMPL (USE_MUX_IMPL),
        .DEVICE       (DEVICE)
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

    mvb_shakedown_property #(
        .RX_ITEMS   (RX_ITEMS),
        .TX_ITEMS   (TX_ITEMS),
        .ITEM_WIDTH (ITEM_WIDTH)
    )
    PROPERTY_CHECK (
        .RESET  (reset.RESET),
        .mvb_rx (mvb_rx),
        .mvb_tx (mvb_tx)
    );

endmodule
