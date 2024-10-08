// tbench.sv: Testbench
// Copyright (C) 2023-2024 CESNET z. s. p. o.
// Author: Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
//         Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

import uvm_pkg::*;
`include "uvm_macros.svh"
import test::*;

module testbench;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Signals
    logic CLK = 0;
    logic RST = 0;

    // ----------------------------e--------------------------------------------------------------------------------------------------------------------------------------
    // Interfaces
    reset_if                                        reset_vif                     (CLK);
    mvb_if #(ITEMS, ITEM_WIDTH + $clog2(TX_PORTS))  rx_mvb_vif                    (CLK);
    mvb_if #(ITEMS, ITEM_WIDTH)                     tx_mvb_vif [TX_PORTS -1 : 0]  (CLK);

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Define clock period
    always #(CLK_PERIOD) CLK = ~CLK;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Start of tests
    initial begin
        uvm_root m_root;
        automatic virtual mvb_if #(ITEMS, ITEM_WIDTH) v_tx_mvb_vif [TX_PORTS -1 : 0] = tx_mvb_vif;

        $timeformat(-9, 5, " ns",10);

        uvm_config_db #(virtual reset_if)                                        ::set(null, "", "reset_vif"  , reset_vif);
        uvm_config_db #(virtual mvb_if #(ITEMS, ITEM_WIDTH + $clog2(TX_PORTS)))  ::set(null, "", "rx_mvb_vif" , rx_mvb_vif);

        // Configuration of database
        for (int i = 0; i < TX_PORTS; i++) begin
            uvm_config_db #(virtual mvb_if #(ITEMS, ITEM_WIDTH))                 ::set(null, "", $sformatf("tx_mvb_vif_%0d", i), v_tx_mvb_vif[i]);
        end

        m_root = uvm_root::get();
        m_root.finish_on_completion = 0;
        m_root.set_report_id_action_hier("ILLEGALNAME",UVM_NO_ACTION);

        uvm_config_db#(int)             ::set(null, "", "recording_detail", 0);
        uvm_config_db#(uvm_bitstream_t) ::set(null, "", "recording_detail", 0);

        run_test();
        $stop(2);
    end

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // DUT
    DUT DUT_U (
        .CLK    (CLK),
        .RST    (reset_vif.RESET),
        .rx_mvb (rx_mvb_vif),
        .tx_mvb (tx_mvb_vif)
    );

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Properties
    mvb_property  #(
        .ITEMS      (ITEMS),
        .ITEM_WIDTH (ITEM_WIDTH)
    ) property_wr (
        .RESET      (reset_vif.RESET),
        .vif        (rx_mvb_vif)
    );

    generate
        if (DEMUX_VERSION != "logic") begin
            for (genvar i = 0; i < TX_PORTS; i++) begin
                mvb_property #(
                    .ITEMS      (ITEMS),
                    .ITEM_WIDTH (ITEM_WIDTH)
                ) property_rd (
                    .RESET      (reset_vif.RESET),
                    .vif        (tx_mvb_vif[i])
                );
            end
        end
    endgenerate
endmodule
