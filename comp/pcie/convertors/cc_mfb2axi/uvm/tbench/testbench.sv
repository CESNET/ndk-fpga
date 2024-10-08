//-- tbench.sv: Testbench
//-- Copyright (C) 2023 CESNET z. s. p. o.
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
    axi_if #(CC_TDATA_WIDTH, CC_TUSER_WIDTH) axi_cc(CLK);
    mfb_if #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0) mfb_cc(CLK);

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
        uvm_config_db#(virtual axi_if #(CC_TDATA_WIDTH, CC_TUSER_WIDTH))::set(null, "", "vif_rx", axi_cc);
        uvm_config_db#(virtual mfb_if #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0))::set(null, "", "vif_tx", mfb_cc);

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
        .axi_cc (axi_cc),
        .mfb_cc (mfb_cc)
    );

endmodule
