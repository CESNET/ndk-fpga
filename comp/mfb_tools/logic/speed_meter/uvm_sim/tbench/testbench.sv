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
    mfb_if #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0) mfb_rx(CLK);
    mfb_if #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0) mfb_tx(CLK);
    mi_if #(MI_DATA_WIDTH, MI_ADDRESS_WIDTH) mi_config(CLK);

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
        uvm_config_db#(virtual mfb_if #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0))::set(null, "", "vif_rx", mfb_rx);
        uvm_config_db#(virtual mfb_if #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0))::set(null, "", "vif_tx", mfb_tx);
        uvm_config_db#(virtual mi_if #(MI_DATA_WIDTH, MI_ADDRESS_WIDTH))::set(null, "", "vif_mi", mi_config);

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
        .CLK       (CLK),
        .RST       (reset.RESET),
        .mfb_rx    (mfb_rx),
        .mfb_tx    (mfb_tx),
        .config_mi (mi_config)
    );

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Properties
    // mvb_property #(
    //     .MVB_ITEMS       (MVB_ITEMS),
    //     .ITEM_WIDTH  (ITEM_WIDTH)
    // )
    // property_rd(
    //     .RESET (reset.RESET),
    //     .vif   (mvb_tx)
    // );

    // mvb_property  #(
    //     .MVB_ITEMS      (MVB_ITEMS),
    //     .ITEM_WIDTH (ITEM_WIDTH)
    // )
    // property_wr (
    //     .RESET (reset.RESET),
    //     .vif   (mvb_rx)
    // );

endmodule
