// tbench.sv: Testbench
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kriz <danielkriz@cesnet.cz>

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

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Interfaces
    reset_if  reset(CLK);
    mfb_if #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, META_WIDTH) mfb_rx(CLK);
    mvb_if #(MVB_ITEMS, MVB_DATA_WIDTH)                                                mvb_tx(CLK);
    mvb_if #(MVB_ITEMS, 1)                                                             mvb_end(CLK);

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Define clock ticking
    always #(CLK_PERIOD) CLK = ~CLK;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Start of tests
    initial begin
        uvm_root m_root;

        // Configuration of database
        uvm_config_db#(virtual reset_if)::set(null, "", "vif_reset", reset);
        uvm_config_db#(virtual mfb_if #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, META_WIDTH))::set(null, "", "vif_rx", mfb_rx);
        uvm_config_db#(virtual mvb_if #(MVB_ITEMS, MVB_DATA_WIDTH))::set(null, "", "vif_mvb_tx", mvb_tx);
        uvm_config_db#(virtual mvb_if #(MVB_ITEMS, 1))::set(null, "", "vif_mvb_end", mvb_end);

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
        .CLK     (CLK),
        .RST     (reset.RESET),
        .mfb_rx  (mfb_rx),
        .mvb_tx  (mvb_tx),
        .mvb_end (mvb_end)
    );

    // Properties
    items_valid_property #(
        .MFB_REGIONS     (MFB_REGIONS),
        .MFB_REGION_SIZE (MFB_REGION_SIZE),
        .MFB_BLOCK_SIZE  (MFB_BLOCK_SIZE),
        .MFB_ITEM_WIDTH  (MFB_ITEM_WIDTH),
        .META_WIDTH      (META_WIDTH),
        .MVB_DATA_WIDTH  (MVB_DATA_WIDTH),
        .MVB_ITEMS       (MVB_ITEMS)
    )
    PROPERTY_CHECK (
        .RESET       (reset.RESET),
        .rx_mfb_vif  (mfb_rx),
        .tx_mvb_vif  (mvb_tx),
        .end_mvb_vif (mvb_end)
    );



endmodule
