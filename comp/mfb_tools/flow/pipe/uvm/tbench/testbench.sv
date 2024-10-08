//-- tbench.sv: Testbench
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author:   David Beneš <xbenes52@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import uvm_pkg::*;
`include "uvm_macros.svh"
import test::*;

module testbench;

    //Signals
    logic CLK = 0;

    //Interfaces
    reset_if reset(CLK);
    mfb_if #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) mfb_wr(CLK);
    mfb_if #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) mfb_rd(CLK);

    //Clock
    always #(CLK_PERIOD) CLK = ~CLK;

    //Start of tests
    initial begin
        uvm_root m_root;

        //Configuration of database
        uvm_config_db#(virtual reset_if)::set(null, "", "vif_reset", reset);
        uvm_config_db#(virtual mfb_if #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))::set(null, "", "vif_rx", mfb_wr);
        uvm_config_db#(virtual mfb_if #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))::set(null, "", "vif_tx", mfb_rd);

        m_root = uvm_root::get();
        m_root.finish_on_completion = 0;
        m_root.set_report_id_action_hier("ILLEGALNAME",UVM_NO_ACTION);

        uvm_config_db#(int)            ::set(null, "", "recording_detail", 0);
        uvm_config_db#(uvm_bitstream_t)::set(null, "", "recording_detail", 0);

        run_test();
        $stop(2);
    end

    //DUT mapping
    DUT DUT_U(
        .CLK        (CLK),
        .RST        (reset.RESET),
        .mfb_wr     (mfb_wr),
        .mfb_rd     (mfb_rd)
    );

    mfb_pipe_property #(
        .REGIONS        (REGIONS),
        .REGION_SIZE    (REGION_SIZE),
        .BLOCK_SIZE     (BLOCK_SIZE),
        .ITEM_WIDTH     (ITEM_WIDTH),
        .META_WIDTH     (META_WIDTH)
    )
    PROPERTY_CHECK (
        .RESET      (reset.RESET),
        .mfb_wr_vif (mfb_wr),
        .mfb_rd_vif (mfb_rd)
    );


endmodule


