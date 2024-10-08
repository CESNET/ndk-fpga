// tbench.sv: Testbench
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

import uvm_pkg::*;
`include "uvm_macros.svh"
import test::*;

module testbench;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Signals
    logic CLK = 0;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Interfaces
    reset_if                                           reset_vif                      (CLK);
    mvb_if #(MVB_ITEMS, MVB_ITEM_WIDTH)                rx_mvb_vif [RX_STREAMS -1 : 0] (CLK);
    mvb_if #(MVB_ITEMS*RX_STREAMS, $clog2(RX_STREAMS)) rx_sel_mvb_vif                 (CLK);
    mvb_if #(MVB_ITEMS*RX_STREAMS, MVB_ITEM_WIDTH)     tx_mvb_vif                     (CLK);

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Define clock period
    always #(CLK_PERIOD) CLK = ~CLK;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Configuration and start of tests
    initial begin
        uvm_root m_root;

        automatic virtual mvb_if #(MVB_ITEMS, MVB_ITEM_WIDTH) v_rx_mvb_vif [RX_STREAMS - 1 : 0] = rx_mvb_vif;

        // Configuration of the database
        uvm_config_db #(virtual reset_if)                                           ::set(null, "", "reset_vif",                        reset_vif);
        for (int port = 0; port < RX_STREAMS; port++) begin
            uvm_config_db #(virtual mvb_if #(MVB_ITEMS, MVB_ITEM_WIDTH))            ::set(null, "", $sformatf("rx_mvb_vif_%0d", port),  v_rx_mvb_vif[port]);
        end

        uvm_config_db #(virtual mvb_if #(MVB_ITEMS*RX_STREAMS, $clog2(RX_STREAMS))) ::set(null, "", "rx_sel_mvb_vif",                   rx_sel_mvb_vif);
        uvm_config_db #(virtual mvb_if #(MVB_ITEMS*RX_STREAMS, MVB_ITEM_WIDTH))     ::set(null, "", "tx_mvb_vif",                       tx_mvb_vif);

        m_root = uvm_root::get();
        m_root.finish_on_completion = 0;
        m_root.set_report_id_action_hier("ILLEGALNAME", UVM_NO_ACTION);

        uvm_config_db#(int)            ::set(null, "", "recording_detail", 0);
        uvm_config_db#(uvm_bitstream_t)::set(null, "", "recording_detail", 0);

        run_test();
        $stop(2);
    end

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // DUT
    DUT DUT_U (
        .CLK        (CLK),
        .RST        (reset_vif.RESET),
        .rx_mvb     (rx_mvb_vif),
        .rx_sel_mvb (rx_sel_mvb_vif),
        .tx_mvb     (tx_mvb_vif)
    );

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Properties
    merge_streams_ordered_property #(
        .MVB_ITEMS      (MVB_ITEMS),
        .MVB_ITEM_WIDTH (MVB_ITEM_WIDTH),
        .RX_STREAMS     (RX_STREAMS)
    ) TB_PROPERTY_CHECK (
        .RESET          (reset_vif.RESET),
        .rx_mvb_vif     (rx_mvb_vif),
        .rx_sel_mvb_vif (rx_sel_mvb_vif),
        .tx_mvb_vif     (tx_mvb_vif)
    );

endmodule
