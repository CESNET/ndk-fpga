// tbench.sv: Testbench
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


import uvm_pkg::*;
`include "uvm_macros.svh"
import test::*;

module testbench;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Signals
    logic CLK = 0;
    logic RST = 0;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Interfaces
    reset_if  reset(CLK);
    mfb_if #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0) mfb_tx(CLK);
    axi_if #(DATA_WIDTH, TUSER_WIDTH) axi_rx(CLK);

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Define clock ticking
    always #(CLK_PERIOD) CLK = ~CLK;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Start of tests
    initial begin
        uvm_root m_root;

        // Configuration of database
        uvm_config_db#(virtual reset_if)::set(null, "", "vif_reset", reset);
        uvm_config_db#(virtual mfb_if #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0))::set(null, "", "vif_tx", mfb_tx);
        uvm_config_db#(virtual axi_if #(DATA_WIDTH, TUSER_WIDTH))::set(null, "", "vif_rx", axi_rx);

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
        .mfb_tx     (mfb_tx),
        .axi_rx     (axi_rx)
    );

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Properties

    ////////////////////////////////////
    // RX PROPERTY
    mfb_property #(
        .REGIONS     (REGIONS),
        .REGION_SIZE (REGION_SIZE),
        .BLOCK_SIZE  (BLOCK_SIZE),
        .ITEM_WIDTH  (ITEM_WIDTH),
        .META_WIDTH  (0)
    )
    MFB_RX (
        .RESET (reset.RESET),
        .vif   (mfb_tx)
    );


    ////////////////////////////////////
    // TX PROPERTY
    axi_property MFB_TX (
        .RESET (reset.RESET),
        .vif   (axi_rx)
    );

endmodule
