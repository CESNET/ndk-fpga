// tbench.sv: Testbench
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Tomas Hak <xhakto01@vut.cz>

// SPDX-License-Identifier: BSD-3-Clause


import uvm_pkg::*;
`include "uvm_macros.svh"
import test::*;

module testbench;

    // Signals
    logic CLK = 0;

    // Interfaces
    reset_if reset(CLK);
    mi_if  #(MI_DATA_WIDTH, MI_ADDR_WIDTH) mi(CLK);
    mfb_if #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH) mfb_rx(CLK);
    mfb_if #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH) mfb_tx(CLK);

    // Define clock ticking
    always #(CLK_PERIOD) CLK = ~CLK;

    // Start of tests
    initial begin
        uvm_root m_root;

        // Configuration of database
        uvm_config_db#(virtual reset_if)::set(null, "", "vif_reset", reset);
        uvm_config_db#(virtual mi_if  #(MI_DATA_WIDTH, MI_ADDR_WIDTH))::set(null, "", "vif_mi", mi);
        uvm_config_db#(virtual mfb_if #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH))::set(null, "", "vif_rx", mfb_rx);
        uvm_config_db#(virtual mfb_if #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH))::set(null, "", "vif_tx", mfb_tx);

        m_root = uvm_root::get();
        m_root.finish_on_completion = 0;
        m_root.set_report_id_action_hier("ILLEGALNAME",UVM_NO_ACTION);

        //stop unnecessary recording
        uvm_config_db#(int)            ::set(null, "", "recording_detail", 0);
        uvm_config_db#(uvm_bitstream_t)::set(null, "", "recording_detail", 0);

        run_test();
        $stop(2);
    end

    // DUT
    DUT DUT_U (
        .CLK        (CLK),
        .RST        (reset.RESET),
        .mi         (mi),
        .mfb_rx     (mfb_rx),
        .mfb_tx     (mfb_tx)
    );

    // Properties
    rate_limiter_property #(
        .MFB_REGIONS     (MFB_REGIONS),
        .MFB_REGION_SIZE (MFB_REGION_SIZE),
        .MFB_BLOCK_SIZE  (MFB_BLOCK_SIZE),
        .MFB_ITEM_WIDTH  (MFB_ITEM_WIDTH),
        .MFB_META_WIDTH  (MFB_META_WIDTH)
    )
    PROPERTY_CHECK (
        .RESET      (reset.RESET),
        .tx_mfb_vif (mfb_tx),
        .rx_mfb_vif (mfb_rx)
    );

endmodule
