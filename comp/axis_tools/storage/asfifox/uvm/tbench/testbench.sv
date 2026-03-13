//-- testbench.sv: Testbench
//-- Copyright (C) 2026 CESNET z. s. p. o.
//-- Author(s): Tomáš Neckař <xneckat00@stud.fit.vut.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


import uvm_pkg::*;
`include "uvm_macros.svh"
import uvm_generic::*;
import uvm_axi::*;

module testbench;

    localparam int unsigned TUSER_WIDTH = 0;

    // Register test with parameters in UVM factory.
    typedef test::base#(
        .ITEMS      (ITEMS),
        .ITEM_WIDTH (ITEM_WIDTH)
    ) base;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Signals
    logic CLK_RX = 0;
    logic CLK_TX = 0;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Interfaces
    reset_if reset_rx (CLK_RX);
    reset_if reset_tx (CLK_TX);

    axi_if #(
        .ITEMS          (ITEMS),
        .ITEM_WIDTH     (ITEM_WIDTH),
        .TUSER_WIDTH    (TUSER_WIDTH)
    ) axi_rx (CLK_RX);
    axi_if #(
        .ITEMS          (ITEMS),
        .ITEM_WIDTH     (ITEM_WIDTH),
        .TUSER_WIDTH    (TUSER_WIDTH)
    ) axi_tx (CLK_TX);

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Define clock period
    always begin #(CLK_RX_PERIOD) CLK_RX = ~CLK_RX; end
    always begin #(CLK_TX_PERIOD) CLK_TX = ~CLK_TX; end

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Start of tests
    initial begin
        uvm_root m_root;

        // REGISTER INTERFACE INTO DATABASE
        uvm_config_db #(virtual reset_if)::set(null, "", "vif_reset_rx", reset_rx);
        uvm_config_db #(virtual reset_if)::set(null, "", "vif_reset_tx", reset_tx);
        uvm_config_db #(virtual axi_if #(.ITEMS(ITEMS), .ITEM_WIDTH(ITEM_WIDTH), .TUSER_WIDTH(TUSER_WIDTH)))
            ::set(null, "", "vif_axi_rx", axi_rx);
        uvm_config_db #(virtual axi_if #(.ITEMS(ITEMS), .ITEM_WIDTH(ITEM_WIDTH), .TUSER_WIDTH(TUSER_WIDTH)))
            ::set(null, "", "vif_axi_tx", axi_tx);

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
    AXIS_ASFIFOX #(
        .TDATA_WIDTH    (ITEMS * ITEM_WIDTH),
        .TUSER_WIDTH    (uvm_generic::TUSER_WIDTH),
        .FIFO_ITEMS     (FIFO_ITEMS),
        .RAM_TYPE       (RAM_TYPE),
        .FWFT_MODE      (FWFT_MODE),
        .OUTPUT_REG     (OUTPUT_REG),
        .AFULL_OFFSET   (AFULL_OFFSET),
        .AEMPTY_OFFSET  (AEMPTY_OFFSET),
        .DEVICE         (DEVICE)
    ) VHDL_DUT_U (

        // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
        // RX AXI-Stream interface (RX_CLK)
        // -------------------------------------------------------------------------------------------------------------------------------------------------------------------

        .RX_CLK            (CLK_RX),
        .RX_RESET          (reset_rx.RESET),

        .RX_AXIS_TDATA     (axi_rx.TDATA),
        .RX_AXIS_TUSER     (axi_rx.TUSER),
        .RX_AXIS_TKEEP     (axi_rx.TKEEP),
        .RX_AXIS_TLAST     (axi_rx.TLAST),
        .RX_AXIS_TVALID    (axi_rx.TVALID),
        .RX_AXIS_TREADY    (axi_rx.TREADY),

        .RX_FIFO_AFULL     (),
        .RX_FIFO_STATUS    (),

        // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
        // TX AXI-Stream interface (TX_CLK)
        // -------------------------------------------------------------------------------------------------------------------------------------------------------------------

        .TX_CLK            (CLK_TX),
        .TX_RESET          (reset_tx.RESET),

        .TX_AXIS_TDATA     (axi_tx.TDATA),
        .TX_AXIS_TUSER     (axi_tx.TUSER),
        .TX_AXIS_TKEEP     (axi_tx.TKEEP),
        .TX_AXIS_TLAST     (axi_tx.TLAST),
        .TX_AXIS_TVALID    (axi_tx.TVALID),
        .TX_AXIS_TREADY    (axi_tx.TREADY),

        .TX_FIFO_AEMPTY    (),
        .TX_FIFO_STATUS    ()

    );

endmodule
