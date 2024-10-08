//-- tbench.sv: Testbench
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import uvm_pkg::*;
`include "uvm_macros.svh"
import test::*;

module testbench;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Signals
    logic CLK = 0;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Interfaces
    reset_if                            reset  (CLK);
    mvb_if #(RX0_ITEMS, RX0_ITEM_WIDTH) mvb_rx0(CLK);
    mvb_if #(RX1_ITEMS, RX1_ITEM_WIDTH) mvb_rx1(CLK);
    mvb_if #(RX0_ITEMS, TX_ITEM_WIDTH)  mvb_tx (CLK);
    mvb_if #(RX0_ITEMS, RX0_ITEM_WIDTH) mvb_tx0(CLK);
    mvb_if #(RX0_ITEMS, RX1_ITEM_WIDTH) mvb_tx1(CLK);

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Define clock period
    always #(CLK_PERIOD) CLK = ~CLK;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Start of tests
    initial begin
        uvm_root m_root;

        // Configuration of database
        uvm_config_db #(virtual reset_if)                           ::set(null, "", "vif_reset", reset);
        uvm_config_db #(virtual mvb_if #(RX0_ITEMS, RX0_ITEM_WIDTH))::set(null, "", "vif_rx0",   mvb_rx0);
        uvm_config_db #(virtual mvb_if #(RX1_ITEMS, RX1_ITEM_WIDTH))::set(null, "", "vif_rx1",   mvb_rx1);
        uvm_config_db #(virtual mvb_if #(RX0_ITEMS, TX_ITEM_WIDTH)) ::set(null, "", "vif_tx",    mvb_tx );
        uvm_config_db #(virtual mvb_if #(RX0_ITEMS, RX0_ITEM_WIDTH))::set(null, "", "vif_tx0",   mvb_tx0);
        uvm_config_db #(virtual mvb_if #(RX0_ITEMS, RX1_ITEM_WIDTH))::set(null, "", "vif_tx1",   mvb_tx1);

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
        .CLK     (CLK        ),
        .RST     (reset.RESET),
        .mvb_rx0 (mvb_rx0    ),
        .mvb_rx1 (mvb_rx1    ),
        .mvb_tx  (mvb_tx     ),
        .mvb_tx0 (mvb_tx0    ),
        .mvb_tx1 (mvb_tx1    )
    );

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Properties
    merge_items_property #(
        .RX0_ITEMS      (RX0_ITEMS     ),
        .RX0_ITEM_WIDTH (RX0_ITEM_WIDTH),
        .RX1_ITEMS      (RX1_ITEMS     ),
        .RX1_ITEM_WIDTH (RX1_ITEM_WIDTH),
        .TX_ITEM_WIDTH  (TX_ITEM_WIDTH )
    )
    PROPERTY_CHECK (
        .RESET       (reset.RESET),
        .mvb_rx0_vif (mvb_rx0    ),
        .mvb_rx1_vif (mvb_rx1    ),
        .mvb_tx_vif  (mvb_tx     ),
        .mvb_tx0_vif (mvb_tx0    ),
        .mvb_tx1_vif (mvb_tx1    )
    );

endmodule
