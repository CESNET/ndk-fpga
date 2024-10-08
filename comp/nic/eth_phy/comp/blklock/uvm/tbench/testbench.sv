/*
 * file       : testbench.sv
 * Copyright (C) 2022 CESNET z. s. p. o.
 * description: Testbench for Block Lock
 * date       : 2022
 * author     : Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

import uvm_pkg::*;
`include "uvm_macros.svh"
import test::*;

module testbench;

    localparam ITEM_WIDTH = 8;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Signals
    logic CLK = 0;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Interfaces
    mvb_if #(1, 2)  mvb_rx(CLK);
    mvb_if #(1, 2)  mvb_tx(CLK);
    reset_if        rst_if(CLK);

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Define clock period
    always #(CLK_PERIOD) CLK = ~CLK;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Start of tests
    initial begin
        uvm_root m_root;

        uvm_config_db#(virtual mvb_if #(1, 2))::set(null, "", "vif_rx", mvb_rx);
        uvm_config_db#(virtual mvb_if #(1, 2))::set(null, "", "vif_tx", mvb_tx);
        uvm_config_db#(virtual reset_if)::set(null, "", "rst_vif", rst_if);

        m_root = uvm_root::get();

        m_root.finish_on_completion = 0;
        m_root.set_report_id_action_hier("ILLEGALNAME",UVM_NO_ACTION);

        run_test();
        $stop(2);
    end

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // DUT
    DUT DUT_U (
        .CLK        (CLK),
        .rst_if     (rst_if),
        .mvb_wr     (mvb_rx),
        .mvb_rd     (mvb_tx)
    );

endmodule
