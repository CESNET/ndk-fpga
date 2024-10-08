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

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Interfaces
    reset_if  reset(CLK);
    mfb_if #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, META_WIDTH) mfb_rx(CLK);
    mvb_if #(MFB_REGIONS, MVB_DATA_WIDTH+1+MFB_META_WIDTH) mvb_tx(CLK);

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
        uvm_config_db#(virtual mvb_if #(MFB_REGIONS, MVB_DATA_WIDTH+1+MFB_META_WIDTH))::set(null, "", "vif_mvb_tx", mvb_tx);

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
        .CLK    (CLK),
        .RST    (reset.RESET),
        .mfb_rx (mfb_rx),
        .mvb_tx (mvb_tx)
    );

    // Properties
    checksum_calculator_property #(
        .MFB_REGIONS     (MFB_REGIONS),
        .MFB_REGION_SIZE (MFB_REGION_SIZE),
        .MFB_BLOCK_SIZE  (MFB_BLOCK_SIZE),
        .MFB_ITEM_WIDTH  (MFB_ITEM_WIDTH),
        .META_WIDTH      (META_WIDTH),
        .MVB_DATA_WIDTH  (MVB_DATA_WIDTH+1+MFB_META_WIDTH)
    )
    PROPERTY_CHECK (
        .RESET      (reset.RESET),
        .rx_mfb_vif (mfb_rx),
        .tx_mvb_vif (mvb_tx)
    );



endmodule
