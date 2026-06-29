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
    logic RST_INIT = 1'b1;

    always begin
        #(CLK_PERIOD) CLK = ~CLK;
    end

    // ---------- //
    // Interfaces //
    // ---------- //

    reset_if                                                                               reset (CLK);
   mfb_if #(
       .REGIONS     (MFB_REGIONS),
       .REGION_SIZE (MFB_REGION_SIZE),
       .BLOCK_SIZE  (MFB_BLOCK_SIZE),
       .ITEM_WIDTH  (MFB_ITEM_WIDTH),
       .META_WIDTH  (0)
   )              mfb_rx(CLK);
   mvb_if #(
       .ITEMS      (MFB_REGIONS),
       .ITEM_WIDTH (RX_MVB_ITEM_WIDTH)
   )                                               mvb_rx(CLK);
   mfb_if #(
       .REGIONS     (MFB_REGIONS),
       .REGION_SIZE (MFB_REGION_SIZE),
       .BLOCK_SIZE  (MFB_BLOCK_SIZE),
       .ITEM_WIDTH  (MFB_ITEM_WIDTH),
       .META_WIDTH  (USERMETA_WIDTH)
   ) mfb_tx(CLK);
   mvb_if #(
       .ITEMS      (MFB_REGIONS),
       .ITEM_WIDTH (USERMETA_WIDTH)
   )                                                  mvb_tx(CLK);

    // ----- //
    // Tests //
    // ----- //

    typedef test::test_base #(
        .MFB_REGIONS       (MFB_REGIONS),
        .MFB_REGION_SIZE   (MFB_REGION_SIZE),
        .MFB_BLOCK_SIZE    (MFB_BLOCK_SIZE),
        .MFB_ITEM_WIDTH    (MFB_ITEM_WIDTH),
        .PKT_MTU           (PKT_MTU),
        .USERMETA_WIDTH    (USERMETA_WIDTH),
        .RX_MVB_ITEM_WIDTH (RX_MVB_ITEM_WIDTH)
    ) test_base;
    typedef test::test_speed #(
        .MFB_REGIONS       (MFB_REGIONS),
        .MFB_REGION_SIZE   (MFB_REGION_SIZE),
        .MFB_BLOCK_SIZE    (MFB_BLOCK_SIZE),
        .MFB_ITEM_WIDTH    (MFB_ITEM_WIDTH),
        .PKT_MTU           (PKT_MTU),
        .USERMETA_WIDTH    (USERMETA_WIDTH),
        .RX_MVB_ITEM_WIDTH (RX_MVB_ITEM_WIDTH)
    ) test_speed;


    initial begin #(4*CLK_PERIOD) RST_INIT <= 1'b0; end

    // Start of tests
    initial begin
        uvm_root m_root;

        // ---------------------- //
        // Database configuration //
        // ---------------------- //

        uvm_config_db #(virtual reset_if)                                                                              ::set(null, "", "vif_reset",  reset);
        uvm_config_db #(virtual mfb_if #(
            .REGIONS     (MFB_REGIONS),
            .REGION_SIZE (MFB_REGION_SIZE),
            .BLOCK_SIZE  (MFB_BLOCK_SIZE),
            .ITEM_WIDTH  (MFB_ITEM_WIDTH),
            .META_WIDTH  (0)
        ))             ::set(null, "", "vif_rx_mfb", mfb_rx);
        uvm_config_db #(virtual mvb_if #(
            .ITEMS      (MFB_REGIONS),
            .ITEM_WIDTH (RX_MVB_ITEM_WIDTH)
        ))                                              ::set(null, "", "vif_rx_mvb", mvb_rx);
        uvm_config_db #(virtual mfb_if #(
            .REGIONS     (MFB_REGIONS),
            .REGION_SIZE (MFB_REGION_SIZE),
            .BLOCK_SIZE  (MFB_BLOCK_SIZE),
            .ITEM_WIDTH  (MFB_ITEM_WIDTH),
            .META_WIDTH  (USERMETA_WIDTH)
        ))::set(null, "", "vif_tx_mfb", mfb_tx);
        uvm_config_db #(virtual mvb_if #(
            .ITEMS      (MFB_REGIONS),
            .ITEM_WIDTH (USERMETA_WIDTH)
        ))                                                 ::set(null, "", "vif_tx_mvb", mvb_tx);

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
        .MFB_REGIONS       (MFB_REGIONS),
        .MFB_REGION_SIZE   (MFB_REGION_SIZE),
        .MFB_BLOCK_SIZE    (MFB_BLOCK_SIZE),
        .MFB_ITEM_WIDTH    (MFB_ITEM_WIDTH),
        .PKT_MTU           (PKT_MTU),
        .MVB_FIFO_DEPTH    (MVB_FIFO_DEPTH),
        .MFB_FIFO_DEPTH    (MFB_FIFO_DEPTH),
        .USERMETA_WIDTH    (USERMETA_WIDTH),
        .DEVICE            (DEVICE),
        .RX_MVB_ITEM_WIDTH (RX_MVB_ITEM_WIDTH)
    )
    DUT_U
    (
        .CLK    (CLK),
        .RST    (reset.RESET | RST_INIT),
        .mfb_rx (mfb_rx),
        .mvb_rx (mvb_rx),
        .mfb_tx (mfb_tx),
        .mvb_tx (mvb_tx)
    );

    // -------- //
    // Property //
    // -------- //

    mfb_frame_extender_property #(
        .MFB_REGIONS       (MFB_REGIONS),
        .MFB_REGION_SIZE   (MFB_REGION_SIZE),
        .MFB_BLOCK_SIZE    (MFB_BLOCK_SIZE),
        .MFB_ITEM_WIDTH    (MFB_ITEM_WIDTH),
        .USERMETA_WIDTH    (USERMETA_WIDTH),
        .RX_MVB_ITEM_WIDTH (RX_MVB_ITEM_WIDTH)
    )
    PROPERTY_CHECK (
        .RESET  (reset.RESET | RST_INIT),
        .mfb_rx (mfb_rx),
        .mvb_rx (mvb_rx),
        .mfb_tx (mfb_tx),
        .mvb_tx (mvb_tx)
    );


endmodule
