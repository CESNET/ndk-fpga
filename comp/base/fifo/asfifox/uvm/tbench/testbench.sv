//-- tbench.sv: Testbench
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import uvm_pkg::*;
`include "uvm_macros.svh"
import test::*;

module testbench;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Signals
    logic RX_CLK = 0;
    logic RX_RST = 0;

    logic TX_CLK = 0;
    logic TX_RST = 0;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Interfaces
    mvb_if #(1, ITEM_WIDTH) mvb_wr(RX_CLK);
    reset_if                reset_wr(RX_CLK);

    mvb_if #(1, ITEM_WIDTH) mvb_rd(TX_CLK);
    reset_if                reset_rd(TX_CLK);

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Define clock period
    always #(RX_CLK_PERIOD) RX_CLK = ~RX_CLK;
    always #(TX_CLK_PERIOD) TX_CLK = ~TX_CLK;


    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Start of tests
    initial begin
        uvm_root m_root;
        // Configuration of database
        uvm_config_db#(virtual mvb_if #(1, ITEM_WIDTH))::set(null, "", "vif_rx", mvb_wr);
        uvm_config_db#(virtual reset_if)::set(null, "", "reset_if_rx", reset_wr);
        uvm_config_db#(virtual mvb_if #(1, ITEM_WIDTH))::set(null, "", "vif_tx", mvb_rd);
        uvm_config_db#(virtual reset_if)::set(null, "", "reset_if_tx", reset_rd);

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
        .RX_CLK     (RX_CLK),
        .RX_RST     (reset_wr.RESET),
        .TX_CLK     (TX_CLK),
        .TX_RST     (reset_rd.RESET),
        .mvb_wr     (mvb_wr),
        .mvb_rd     (mvb_rd)
    );

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Properties
    mvb_property #(
        .ITEMS       (1),
        .ITEM_WIDTH  (ITEM_WIDTH)
    )
    property_rd(
        .RESET  (reset_rd.RESET),
        .vif    (mvb_rd)
    );

    mvb_property  #(
        .ITEMS       (1),
        .ITEM_WIDTH  (ITEM_WIDTH)
    )
    property_wr (
        .RESET  (reset_wr.RESET),
        .vif    (mvb_wr)
    );

endmodule
