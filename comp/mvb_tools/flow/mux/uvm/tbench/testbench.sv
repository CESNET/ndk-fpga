//-- tbench.sv: Testbench
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author:   Oliver Gurka <xgurka00@stud.fit.vutbr.cz>

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
    mvb_if #(ITEMS, ITEM_WIDTH) mvb_rd (CLK);
    mvb_if #(1, SEL_WIDTH) mvb_sel (CLK);
    mvb_if #(ITEMS, ITEM_WIDTH) mvb_wr[RX_MVB_CNT - 1 : 0] (CLK);

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Define clock period
    always #(CLK_PERIOD) CLK = ~CLK;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Start of tests
    initial begin
        uvm_root m_root;

        automatic virtual mvb_if #(ITEMS, ITEM_WIDTH) v_mvb_wr[RX_MVB_CNT - 1 : 0] = mvb_wr;

        // Configuration of database
        for (int port = 0; port < RX_MVB_CNT; port++) begin
            uvm_config_db #(virtual mvb_if #(ITEMS, ITEM_WIDTH))::set(null, "", $sformatf("rx_vif_%0d", port), v_mvb_wr[port]);
        end

        uvm_config_db #(virtual reset_if)::set(null, "", "vif_reset", reset);
        uvm_config_db #(virtual mvb_if #(ITEMS, ITEM_WIDTH))::set(null, "", "tx_vif", mvb_rd);
        uvm_config_db #(virtual mvb_if #(1, SEL_WIDTH))::set(null, "", "sel_vif", mvb_sel);

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
        .CLK     (CLK),
        .RST     (reset.RESET),
        .mvb_wr  (mvb_wr),
        .mvb_sel (mvb_sel),
        .mvb_rd  (mvb_rd)
    );

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Properties
    for (genvar port = 0; port < RX_MVB_CNT; port++) begin
        mvb_property #(
            .ITEMS       (ITEMS),
            .ITEM_WIDTH  (ITEM_WIDTH)
        )
        property_rd(
            .RESET (reset.RESET),
            .vif   (mvb_wr[port])
        );
    end


    mvb_property  #(
        .ITEMS      (ITEMS),
        .ITEM_WIDTH (ITEM_WIDTH)
    )
    property_wr (
        .RESET (reset.RESET),
        .vif   (mvb_rd)
    );

endmodule
