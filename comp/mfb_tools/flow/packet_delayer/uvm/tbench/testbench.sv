// testbench.sv: Testbench
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
// SPDX-License-Identifier: BSD-3-Clause

import uvm_pkg::*;
`include "uvm_macros.svh"
import test::*;

module testbench;

    typedef virtual mfb_if #(
        .REGIONS     (REGIONS),
        .REGION_SIZE (REGION_SIZE),
        .BLOCK_SIZE  (BLOCK_SIZE),
        .ITEM_WIDTH  (ITEM_WIDTH),
        .META_WIDTH  (EXTENDED_META_WIDTH)
    ) vif_rx_t;
    typedef virtual mfb_if #(
        .REGIONS     (REGIONS),
        .REGION_SIZE (REGION_SIZE),
        .BLOCK_SIZE  (BLOCK_SIZE),
        .ITEM_WIDTH  (ITEM_WIDTH),
        .META_WIDTH  (META_WIDTH)
    ) vif_tx_t;

    logic          CLK = 0;
    logic          RST = 0;
    logic [64-1:0] CURRENT_TIME;
    logic          PAUSE_REQUEST;

    // ------------------------------------------------------------------------
    // Clock and time source

    always begin
        #(CLK_PERIOD/2) CLK = ~CLK;
    end

    // RST only resets the CURRENT_TIME counter (the DUT reset is driven by the
    // UVM reset agent). The DUT uses only the difference of two consecutive
    // values, so one timestamp unit = one clock period.
    initial begin
        RST = 1;
        #(RESET_CLKS*CLK_PERIOD);
        RST = 0;
    end

    always @(posedge CLK) begin
        if (RST) begin
            CURRENT_TIME <= 64'd0;
        end else begin
            CURRENT_TIME <= CURRENT_TIME + 64'd1;
        end
    end

    // ------------------------------------------------------------------------
    // Interfaces

    reset_if      reset(CLK);
    // RESET = 1 until the reset agent drives it (an X reset would not disable
    // the MFB protocol assertions at the first clock edges)
    pullup(reset.RESET);
    reset_if      time_reset(CLK);
    pulldown(time_reset.RESET);
    pause_if      pause(CLK);
    mfb_if #(
        .REGIONS     (REGIONS),
        .REGION_SIZE (REGION_SIZE),
        .BLOCK_SIZE  (BLOCK_SIZE),
        .ITEM_WIDTH  (ITEM_WIDTH),
        .META_WIDTH  (EXTENDED_META_WIDTH)
    ) mfb_rx(CLK);
    mfb_if #(
        .REGIONS     (REGIONS),
        .REGION_SIZE (REGION_SIZE),
        .BLOCK_SIZE  (BLOCK_SIZE),
        .ITEM_WIDTH  (ITEM_WIDTH),
        .META_WIDTH  (META_WIDTH)
    ) mfb_tx(CLK);

    // TX agent is passive: downstream is always ready, so the release time is
    // driven only by the timestamps, not by output backpressure
    assign mfb_tx.DST_RDY      = 1'b1;
    assign pause.PAUSE_REQUEST = PAUSE_REQUEST;

    // ------------------------------------------------------------------------
    // DUT and MFB protocol checks

    dut DUT_U (
        .CLK           (CLK),
        .RST           (reset.RESET),
        .TIME_RESET    (time_reset.RESET),
        .CURRENT_TIME  (CURRENT_TIME),
        .PAUSE_REQUEST (PAUSE_REQUEST),
        .mfb_rx        (mfb_rx),
        .mfb_tx        (mfb_tx)
    );

    packet_delayer_property #(
        .MFB_REGIONS       (REGIONS),
        .MFB_REGION_SIZE   (REGION_SIZE),
        .MFB_BLOCK_SIZE    (BLOCK_SIZE),
        .MFB_ITEM_WIDTH    (ITEM_WIDTH),
        .RX_MFB_META_WIDTH (EXTENDED_META_WIDTH),
        .TX_MFB_META_WIDTH (META_WIDTH)
    ) PROPERTY_CHECK (
        .RESET      (reset.RESET),
        .tx_mfb_vif (mfb_tx),
        .rx_mfb_vif (mfb_rx)
    );

    // ------------------------------------------------------------------------
    // UVM

    initial begin
        uvm_root m_root;

        uvm_config_db#(virtual reset_if)     ::set(null, "", "vif_reset",      reset);
        uvm_config_db#(virtual reset_if)     ::set(null, "", "vif_time_reset", time_reset);
        uvm_config_db#(virtual pause_if)     ::set(null, "", "vif_pause",      pause);
        uvm_config_db#(vif_rx_t)             ::set(null, "", "vif_rx",         mfb_rx);
        uvm_config_db#(vif_tx_t)             ::set(null, "", "vif_tx",         mfb_tx);

        m_root = uvm_root::get();
        m_root.finish_on_completion = 0;
        m_root.set_report_id_action_hier("ILLEGALNAME", UVM_NO_ACTION);

        uvm_config_db#(int)            ::set(null, "", "recording_detail", 0);
        uvm_config_db#(uvm_bitstream_t)::set(null, "", "recording_detail", 0);

        run_test();
        $stop(2);
    end

endmodule
