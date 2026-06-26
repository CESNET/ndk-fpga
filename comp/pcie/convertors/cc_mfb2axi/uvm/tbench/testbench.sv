//-- tbench.sv: Testbench
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import uvm_pkg::*;
`include "uvm_macros.svh"
import test::*;

module testbench;

    localparam ITEMS       = MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE;
    localparam ITEM_WIDTH  = 32;
    localparam TUSER_WIDTH = uvm_pcie_axi::tuser_width_get(ITEMS, uvm_pcie_axi::AXI_CC);

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Signals
    logic CLK = 0;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Interfaces
    reset_if  reset(CLK);
    pullup (reset.RESET);

    axi_if #(
        .ITEMS       (ITEMS),
        .ITEM_WIDTH  (32),
        .TUSER_WIDTH (TUSER_WIDTH)
    ) axi_cc(CLK);
    mfb_if #(
        .REGIONS (MFB_REGIONS),
        .REGION_SIZE (MFB_REGION_SIZE),
        .BLOCK_SIZE (MFB_BLOCK_SIZE),
        .ITEM_WIDTH (ITEM_WIDTH),
        .META_WIDTH (0)
    ) mfb_cc(CLK);

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Define clock period
    always #(CLK_PERIOD) CLK = ~CLK;


    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Start of tests
    initial begin
        uvm_root m_root;
        // Configuration of database
        uvm_config_db#(virtual reset_if)::set(null, "", "vif_reset", reset);
        uvm_config_db#(virtual axi_if #(
            .ITEMS       (ITEMS),
            .ITEM_WIDTH  (32),
            .TUSER_WIDTH (TUSER_WIDTH)
        ))::set(null, "", "vif_rx_axi", axi_cc);
        uvm_config_db#(virtual mfb_if #(
            .REGIONS     (MFB_REGIONS),
            .REGION_SIZE (MFB_REGION_SIZE),
            .BLOCK_SIZE  (MFB_BLOCK_SIZE),
            .ITEM_WIDTH  (ITEM_WIDTH),
            .META_WIDTH  (0)
        ))::set(null, "", "vif_tx", mfb_cc);

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
    dut #(
        .STRADDLING (STRADDLING)
    )DUT_U (
        .CLK    (CLK),
        .RST    (reset.RESET),
        .axi_cc (axi_cc),
        .mfb_cc (mfb_cc)
    );


    axi_xilinx_property #(
        .ITEMS       (ITEMS),
        .ITEM_WIDTH  (32),
        .TUSER_WIDTH (TUSER_WIDTH),
        .STRADDLING  (test::STRADDLING)
    )
    PROP (
        .RESET (reset.RESET),
        .vif   (axi_cc)
    );
endmodule
