// tbench.sv: Testbench
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

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
    logic RST = 0;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Interfaces
    reset_if  reset(CLK);
    mfb_if #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0)                          mfb_rx(CLK);
    mfb_if #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MVB_ITEM_WIDTH+HEADER_SIZE) mfb_tx(CLK);
    mvb_if #(MFB_REGIONS, MVB_ITEM_WIDTH)                                                              mvb_rx(CLK);
    mvb_if #(MFB_REGIONS, MVB_ITEM_WIDTH+HEADER_SIZE)                                                  mvb_tx(CLK);

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Define clock ticking
    always #(CLK_PERIOD) CLK = ~CLK;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Start of tests
    initial begin
        uvm_root m_root;

        // Configuration of database
        uvm_config_db#(virtual reset_if)::set(null, "", "vif_reset", reset);
        uvm_config_db#(virtual mfb_if #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0))::set(null, "", "vif_rx", mfb_rx);
        uvm_config_db#(virtual mfb_if #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MVB_ITEM_WIDTH+HEADER_SIZE))::set(null, "", "vif_tx", mfb_tx);
        uvm_config_db#(virtual mvb_if #(MFB_REGIONS, MVB_ITEM_WIDTH))::set(null, "", "vif_mvb_rx", mvb_rx);
        uvm_config_db#(virtual mvb_if #(MFB_REGIONS, MVB_ITEM_WIDTH+HEADER_SIZE))::set(null, "", "vif_mvb_tx", mvb_tx);

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
        .RST        (reset.RESET),
        .mfb_rx     (mfb_rx),
        .mfb_tx     (mfb_tx),
        .mvb_rx     (mvb_rx),
        .mvb_tx     (mvb_tx)
    );

    // Properties
    superunpacketer_property #(
        .MFB_REGIONS     (MFB_REGIONS),
        .MFB_REGION_SIZE (MFB_REGION_SIZE),
        .MFB_BLOCK_SIZE  (MFB_BLOCK_SIZE),
        .MFB_ITEM_WIDTH  (MFB_ITEM_WIDTH),
        .MVB_ITEM_WIDTH  (MVB_ITEM_WIDTH),
        .META_WIDTH      (HEADER_SIZE)
    )
    PROPERTY_CHECK (
        .RESET      (reset.RESET),
        .tx_mfb_vif (mfb_tx),
        .rx_mfb_vif (mfb_rx),
        .rx_mvb_vif (mvb_rx),
        .tx_mvb_vif (mvb_tx)
    );



endmodule
