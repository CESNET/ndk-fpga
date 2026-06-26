//-- tbench.sv: Testbench
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import uvm_pkg::*;
`include "uvm_macros.svh"
import test::*;

module testbench;

    localparam AXI_ITEMS = MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE;
    localparam ITEM_WIDTH = 32;
    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Signals
    logic CLK = 0;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Interfaces
    reset_if  reset(CLK);
    axi_if #(AXI_ITEMS, ITEM_WIDTH, uvm_pcie_axi::tuser_width_get(AXI_ITEMS,   uvm_pcie_axi::AXI_CQ)) axi_cq(CLK);
    mfb_if #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, ITEM_WIDTH, 0) mfb_cq(CLK);

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Define clock period
    always #(CLK_PERIOD) CLK = ~CLK;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Start of tests
    initial begin
        uvm_root m_root;
        // Configuration of database
        uvm_config_db#(virtual reset_if)::set(null, "", "vif_reset", reset);
        uvm_config_db#(virtual axi_if #(AXI_ITEMS, ITEM_WIDTH, uvm_pcie_axi::tuser_width_get(AXI_ITEMS,   uvm_pcie_axi::AXI_CQ)))::set(null, "", "vif_rx_axi", axi_cq);
        uvm_config_db#(virtual mfb_if #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, ITEM_WIDTH, 0))::set(null, "", "vif_tx", mfb_cq);

        m_root = uvm_root::get();
        m_root.finish_on_completion = 0;
        m_root.set_report_id_action_hier("ILLEGALNAME",UVM_NO_ACTION);

        uvm_config_db#(int)            ::set(null, "", "recording_detail", 0);
        uvm_config_db#(uvm_bitstream_t)::set(null, "", "recording_detail", 0);

        run_test();
        $stop(2);
    end

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // dut
    dut DUT_U (
        .CLK    (CLK),
        .RST    (reset.RESET),
        .axi_cq (axi_cq),
        .mfb_cq (mfb_cq)
    );

endmodule
