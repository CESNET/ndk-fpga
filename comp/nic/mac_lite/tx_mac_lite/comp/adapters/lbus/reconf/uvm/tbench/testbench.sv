// tbench.sv: Testbench
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Vladislav Valek <xvalek14@vutbr.cz>

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
    mfb_if #(RX_REGIONS, RX_REGION_SIZE, RX_BLOCK_SIZE, RX_ITEM_WIDTH, 0) mfb_rx(CLK);
    mfb_if #(TX_REGIONS, TX_REGION_SIZE, TX_BLOCK_SIZE, TX_ITEM_WIDTH, 0) mfb_tx(CLK);

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Define clock ticking
    always #(CLK_PERIOD) CLK = ~CLK;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Start of tests
    initial begin
        uvm_root m_root;

        // Configuration of database
        uvm_config_db#(virtual reset_if)::set(null, "", "vif_reset", reset);
        uvm_config_db#(virtual mfb_if #(RX_REGIONS, RX_REGION_SIZE, RX_BLOCK_SIZE, RX_ITEM_WIDTH, 0))::set(null, "", "vif_rx", mfb_rx);
        uvm_config_db#(virtual mfb_if #(TX_REGIONS, TX_REGION_SIZE, TX_BLOCK_SIZE, TX_ITEM_WIDTH, 0))::set(null, "", "vif_tx", mfb_tx);

        m_root = uvm_root::get();
        m_root.set_report_id_action_hier("ILLEGALNAME",UVM_NO_ACTION);
        m_root.finish_on_completion = 0;

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
        .mfb_tx     (mfb_tx)
    );

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Properties

    string module_name = "";
    logic START = 1'b1;

    ///////////////////
    // Start check properties after first clock
    initial begin
        $sformat(module_name, "%m");
        @(posedge mfb_tx.CLK)
        #(10ps)
        START = 1'b0;
    end

    ////////////////////////////////////
    // RX PROPERTY
    mfb_property #(
        .REGIONS     (1),
        .REGION_SIZE (8),
        .BLOCK_SIZE  (8),
        .ITEM_WIDTH  (8),
        .META_WIDTH  (0)
    )
    MFB_RX (
        .RESET (reset.RESET),
        .vif   (mfb_rx)
    );


    ////////////////////////////////////
    // TX PROPERTY
    mfb_property #(
        .REGIONS     (1),
        .REGION_SIZE (4),
        .BLOCK_SIZE  (16),
        .ITEM_WIDTH  (8),
        .META_WIDTH  (0)
    )
    MFB_TX (
        .RESET (reset.RESET),
        .vif   (mfb_tx)
    );

    property notfall_src_rdy_inframe;
        @(posedge mfb_tx.CLK) disable iff(reset.RESET || START)
        (mfb_tx.SRC_RDY && (mfb_tx.SOF != 0)) |-> mfb_tx.SRC_RDY s_until_with (mfb_tx.EOF != 0);
    endproperty

    property sof_always_at_begin;
        @(posedge mfb_tx.CLK) disable iff(reset.RESET || START)
        (mfb_tx.SRC_RDY && (mfb_tx.SOF != 0) && (mfb_tx.EOF == 0)) |-> (mfb_tx.SOF_POS == 0);
    endproperty

    property sof_follows_eof;
        @(posedge mfb_tx.CLK) disable iff(reset.RESET || START)
        (mfb_tx.SRC_RDY && (mfb_tx.SOF != 0) && (mfb_tx.EOF != 0) && (mfb_tx.SOF_POS > mfb_tx.EOF_POS[5:4])) |-> (mfb_tx.SOF_POS == mfb_tx.EOF_POS[5:4] + 1);
    endproperty

    assert property (notfall_src_rdy_inframe)
        else begin
            `uvm_error(module_name, "\n\tMFB_TO_LBUS_RECONF/UVM: Making gap inside a frame is not allowed!");
        end

    assert property (sof_always_at_begin)
        else begin
            `uvm_error(module_name, "\n\tMFB_TO_LBUS_RECONF/UVM: When only SOF is present, it needs to be on the beginning of the word!");
        end

    assert property (sof_follows_eof)
        else begin
            `uvm_error(module_name, "\n\tMFB_TO_LBUS_RECONF/UVM: When SOF follows the EOF (e.g. two packets are in the word), the SOF needs to follow immediately after the EOF, no empty blocks shall be between them.");
        end

endmodule
