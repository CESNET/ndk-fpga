// tbench.sv: Testbench
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

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
    reset_if reset (CLK);

    mvb_if #(WRITE_PORTS, DATA_WIDTH) mvb_rx    (CLK);
    mvb_if #(READ_PORTS, DATA_WIDTH)  mvb_tx    (CLK);
    mvb_if #(READ_PORTS, 1)           mvb_rd    (CLK);
    mvb_if #(1, 2)                    mvb_status(CLK);

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Define clock period
    always #(CLK_PERIOD) CLK = ~CLK;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Start of tests
    initial begin
        uvm_root m_root;

        // Configuration of database
        uvm_config_db #(virtual reset_if)::set(null, "", "vif_reset", reset);

        uvm_config_db #(virtual mvb_if #(WRITE_PORTS, DATA_WIDTH))::set(null, "", "vif_mvb_rx",     mvb_rx    );
        uvm_config_db #(virtual mvb_if #(READ_PORTS, DATA_WIDTH)) ::set(null, "", "vif_mvb_tx",     mvb_tx    );
        uvm_config_db #(virtual mvb_if #(READ_PORTS, 1))          ::set(null, "", "vif_mvb_rd",     mvb_rd    );
        uvm_config_db #(virtual mvb_if #(1, 2))                   ::set(null, "", "vif_mvb_status", mvb_status);

        m_root = uvm_root::get();
        m_root.finish_on_completion = 0;
        m_root.set_report_id_action_hier("ILLEGALNAME", UVM_NO_ACTION);

        uvm_config_db #(int)            ::set(null, "", "recording_detail", 0);
        uvm_config_db #(uvm_bitstream_t)::set(null, "", "recording_detail", 0);

        run_test();
        $stop(2);
    end

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // DUT
    DUT DUT_U (
        .CLK (CLK        ),
        .RST (reset.RESET),

        .mvb_rx     (mvb_rx    ),
        .mvb_tx     (mvb_tx    ),
        .mvb_rd     (mvb_rd    ),
        .mvb_status (mvb_status)
    );

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Properties
    fifox_multi_property #(DATA_WIDTH, WRITE_PORTS)
    PROPERTY_CHECK (
        .RESET (reset.RESET),

        .mvb_rx (mvb_rx)
    );

endmodule
