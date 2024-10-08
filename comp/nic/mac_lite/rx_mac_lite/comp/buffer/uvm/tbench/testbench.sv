// tbench.sv: Testbench
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


import uvm_pkg::*;
`include "uvm_macros.svh"
import test_param::*;

module testbench;

    //TESTS
    typedef test::ex_test#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH) ex_test;
    typedef test::speed#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH)   speed;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Signals
    logic RX_CLK = 0;
    logic TX_CLK = 0;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Interfaces
    reset_if reset_rx(RX_CLK);
    reset_if reset_tx(TX_CLK);
    mfb_if #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH) mfb_rx(RX_CLK);
    mfb_if #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0) mfb_tx(TX_CLK);
    mvb_if #(MFB_REGIONS, MFB_META_WIDTH) mvb_tx(TX_CLK);
    // Probes
    bind RX_MAC_LITE_BUFFER : DUT_U.VHDL_DUT_U probe_inf #(2*REGIONS) probe_drop(s_rx_src_rdy_orig_reg, {s_rx_eof_orig_reg, s_rx_force_drop_reg}, RX_CLK);

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Define clock ticking
    always #(RX_CLK_PERIOD) RX_CLK = ~RX_CLK;
    always #(TX_CLK_PERIOD) TX_CLK = ~TX_CLK;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Start of tests
    initial begin
        uvm_root m_root;

        // Configuration of database
        uvm_config_db#(virtual reset_if)::set(null, "", "vif_reset_rx", reset_rx);
        uvm_config_db#(virtual reset_if)::set(null, "", "vif_reset_tx", reset_tx);
        uvm_config_db#(virtual mfb_if #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH))::set(null, "", "vif_rx", mfb_rx);
        uvm_config_db#(virtual mfb_if #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0))::set(null, "", "vif_tx", mfb_tx);
        uvm_config_db#(virtual mvb_if #(MFB_REGIONS, MFB_META_WIDTH))::set(null, "", "vif_mvb_tx", mvb_tx);

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
    DUT #(
        .REGIONS          (MFB_REGIONS)    ,
        .REGION_SIZE      (MFB_REGION_SIZE),
        .BLOCK_SIZE       (MFB_BLOCK_SIZE) ,
        .ITEM_WIDTH       (MFB_ITEM_WIDTH) ,
        .META_WIDTH       (MFB_META_WIDTH) ,
        .DEVICE           (DEVICE)
    ) DUT_U (
        .RX_CLK     (RX_CLK),
        .RX_RST     (reset_rx.RESET),
        .TX_CLK     (TX_CLK),
        .TX_RST     (reset_tx.RESET),
        .mfb_rx     (mfb_rx),
        .mvb_tx     (mvb_tx),
        .mfb_tx     (mfb_tx)
    );

    // Properties
    dut_property #(
        .MFB_REGIONS     (MFB_REGIONS),
        .MFB_REGION_SIZE (MFB_REGION_SIZE),
        .MFB_BLOCK_SIZE  (MFB_BLOCK_SIZE),
        .MFB_ITEM_WIDTH  (MFB_ITEM_WIDTH),
        .MFB_META_WIDTH  (MFB_META_WIDTH)
    )
    PROPERTY_CHECK (
        .RX_RESET   (reset_rx.RESET),
        .TX_RESET   (reset_tx.RESET),
        .tx_mfb_vif (mfb_tx),
        .rx_mfb_vif (mfb_rx),
        .mvb_vif    (mvb_tx)
    );

endmodule
