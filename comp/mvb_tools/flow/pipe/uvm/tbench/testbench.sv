//-- tbench.sv: Testbench
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

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
    mvb_if #(ITEMS, ITEM_WIDTH) mvb_wr(CLK);
    mvb_if #(ITEMS, ITEM_WIDTH) mvb_rd(CLK);

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Define clock period
    always #(CLK_PERIOD) CLK = ~CLK;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Initial reset
    initial begin
        RST = 1;
        #(RESET_CLKS*CLK_PERIOD)
        RST = 0;
    end

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Start of tests
    initial begin
        uvm_root m_root;
        // Configuration of database
        uvm_config_db#(virtual reset_if)::set(null, "", "vif_reset", reset);
        uvm_config_db#(virtual mvb_if #(ITEMS, ITEM_WIDTH))::set(null, "", "vif_rx", mvb_wr);
        uvm_config_db#(virtual mvb_if #(ITEMS, ITEM_WIDTH))::set(null, "", "vif_tx", mvb_rd);

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
        .mvb_wr (mvb_wr),
        .mvb_rd (mvb_rd)
    );

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Properties
    mvb_property #(
        .ITEMS       (ITEMS),
        .ITEM_WIDTH  (ITEM_WIDTH)
    )
    property_rd(
        .RESET (reset.RESET),
        .vif   (mvb_rd)
    );

    mvb_property  #(
        .ITEMS      (ITEMS),
        .ITEM_WIDTH (ITEM_WIDTH)
    )
    property_wr (
        .RESET (reset.RESET),
        .vif   (mvb_wr)
    );

endmodule
