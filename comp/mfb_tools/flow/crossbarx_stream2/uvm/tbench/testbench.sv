// tbench.sv: Testbench
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


import uvm_pkg::*;
`include "uvm_macros.svh"
import test::*;

module testbench;

    //TESTS
    typedef test::ex_test ex_test;
    typedef test::speed speed;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Signals
    logic CLK = 0;
    logic CLK_X2 = 0;
    logic RST = 0;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Interfaces
    reset_if  reset(CLK);
    mfb_if #(RX_MFB_REGIONS, RX_MFB_REGION_S, RX_MFB_BLOCK_S, RX_MFB_ITEM_W, USERMETA_W) mfb_rx(CLK);
    mfb_if #(TX_MFB_REGIONS, TX_MFB_REGION_S, TX_MFB_BLOCK_S, TX_MFB_ITEM_W, USERMETA_W) mfb_tx(CLK);
    mvb_if #(RX_MFB_REGIONS, RX_MVB_ITEM_W) mvb_rx(CLK);
    mvb_if #(TX_MFB_REGIONS, USERMETA_W) mvb_tx(CLK);

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Define clock ticking
    always #(CLK_PERIOD)   CLK = ~CLK;
    always #(CLK_PERIOD/2) CLK_X2 = ~CLK_X2;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Start of tests
    initial begin
        uvm_root m_root;

        // Configuration of database
        uvm_config_db#(virtual reset_if)::set(null, "", "vif_reset", reset);
        uvm_config_db#(virtual mfb_if #(RX_MFB_REGIONS, RX_MFB_REGION_S, RX_MFB_BLOCK_S, RX_MFB_ITEM_W, USERMETA_W))::set(null, "", "vif_rx", mfb_rx);
        uvm_config_db#(virtual mfb_if #(TX_MFB_REGIONS, TX_MFB_REGION_S, TX_MFB_BLOCK_S, TX_MFB_ITEM_W, USERMETA_W))::set(null, "", "vif_tx", mfb_tx);
        uvm_config_db#(virtual mvb_if #(RX_MFB_REGIONS, RX_MVB_ITEM_W))::set(null, "", "vif_mvb_rx", mvb_rx);
        uvm_config_db#(virtual mvb_if #(TX_MFB_REGIONS, USERMETA_W))::set(null, "", "vif_mvb_tx", mvb_tx);

        m_root = uvm_root::get();
        m_root.finish_on_completion = 0;
        m_root.set_report_id_action_hier("ILLEGALNAME",UVM_NO_ACTION);

        uvm_config_db#(int)            ::set(null, "", "recording_detail", 0);
        uvm_config_db#(uvm_bitstream_t)::set(null, "", "recording_detail", 0);

        run_test();
        $stop(2);
    end

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // DUT
    DUT DUT_U (
        .CLK        (CLK),
        .CLK_X2     (CLK_X2),
        .RST        (reset.RESET),
        .mfb_rx     (mfb_rx),
        .mvb_rx     (mvb_rx),
        .mfb_tx     (mfb_tx),
        .mvb_tx     (mvb_tx)
    );

    // Properties
    dut_property #(
        .RX_MFB_REGIONS  (RX_MFB_REGIONS),
        .RX_MFB_REGION_S (RX_MFB_REGION_S),
        .RX_MFB_BLOCK_S  (RX_MFB_BLOCK_S),
        .RX_MFB_ITEM_W   (RX_MFB_ITEM_W),
        .TX_MFB_REGIONS  (TX_MFB_REGIONS),
        .TX_MFB_REGION_S (TX_MFB_REGION_S),
        .TX_MFB_BLOCK_S  (TX_MFB_BLOCK_S),
        .TX_MFB_ITEM_W   (TX_MFB_ITEM_W),
        .RX_MVB_ITEM_W   (RX_MVB_ITEM_W),
        .USERMETA_W      (USERMETA_W)
    )
    PROPERTY_CHECK (
        .RESET      (reset.RESET),
        .rx_mfb_vif (mfb_rx),
        .tx_mfb_vif (mfb_tx),
        .rx_mvb_vif (mvb_rx),
        .tx_mvb_vif (mvb_tx)
    );

endmodule
