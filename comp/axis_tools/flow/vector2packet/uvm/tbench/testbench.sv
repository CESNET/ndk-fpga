// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Tomáš Neckař <xneckat00@stud.fit.vut.cz>
// SPDX-License-Identifier: BSD-3-Clause

import uvm_pkg::*;
`include "uvm_macros.svh"
import uvm_generic::*;

module testbench;
    // Register test with parameters in UVM factory.
    typedef test::base#(
        .RX_ITEMS       (RX_ITEMS),
        .RX_ITEM_WIDTH  (RX_ITEM_WIDTH),
        .TX_ITEMS       (TX_ITEMS),
        .TX_ITEM_WIDTH  (TX_ITEM_WIDTH),
        .TUSER_WIDTH    (TUSER_WIDTH)
    ) base;

    // Create clock
    logic CLK = 0;
    always begin #(CLK_PERIOD/2) CLK = ~CLK; end

    reset_if reset (CLK);
    axi_if #(
        .ITEMS          (RX_ITEMS),
        .ITEM_WIDTH     (RX_ITEM_WIDTH),
        .TUSER_WIDTH    (TUSER_WIDTH)
    ) axi_rx (CLK);
    axi_if #(
        .ITEMS          (TX_ITEMS),
        .ITEM_WIDTH     (TX_ITEM_WIDTH),
        .TUSER_WIDTH    (TUSER_WIDTH)
    ) axi_tx (CLK);

initial begin
        uvm_root m_root;

        // REGISTER INTERFACE INTO DATABASE
        uvm_config_db #(virtual reset_if)::set(null, "", "vif_reset", reset);
        uvm_config_db #(virtual axi_if #(
            .ITEMS(RX_ITEMS), .ITEM_WIDTH(RX_ITEM_WIDTH), .TUSER_WIDTH(TUSER_WIDTH)
        ))::set(null, "", "vif_axi_rx", axi_rx);
        uvm_config_db #(virtual axi_if #(
            .ITEMS(TX_ITEMS), .ITEM_WIDTH(TX_ITEM_WIDTH), .TUSER_WIDTH(TUSER_WIDTH)
        ))::set(null, "", "vif_axi_tx", axi_tx);

        // stop on end of simulation and dont print message ILLEGALNAME
        m_root = uvm_root::get();
        m_root.finish_on_completion = 0;
        m_root.set_report_id_action_hier("ILLEGALNAME", UVM_NO_ACTION);

        // dont record transactions
        uvm_config_db #(int)            ::set(null, "", "recording_detail", 0);
        uvm_config_db #(uvm_bitstream_t)::set(null, "", "recording_detail", 0);

        // RUN TESTS
        run_test();
        // STOP ON END OF SIMULATION
        $stop(2);
    end

    // Instantiate DUT or other VHDL architectures
    AXIS_VECTOR2PACKET #(
        .RX_TDATA_WIDTH      (uvm_generic::RX_TDATA_WIDTH),
        .TX_TDATA_WIDTH      (uvm_generic::TX_TDATA_WIDTH),
        .TUSER_WIDTH         (uvm_generic::TUSER_WIDTH)
    ) VHDL_DUT_U (
        .CLK   (CLK),
        .RESET (reset.RESET),

        .RX_TDATA  (axi_rx.TDATA),
        .RX_TUSER  (axi_rx.TUSER),
        .RX_TVALID (axi_rx.TVALID),
        .RX_TREADY (axi_rx.TREADY),

        .TX_TDATA  (axi_tx.TDATA),
        .TX_TUSER  (axi_tx.TUSER),
        .TX_TKEEP  (axi_tx.TKEEP),
        .TX_TLAST  (axi_tx.TLAST),
        .TX_TVALID (axi_tx.TVALID),
        .TX_TREADY (axi_tx.TREADY)
    );
endmodule
