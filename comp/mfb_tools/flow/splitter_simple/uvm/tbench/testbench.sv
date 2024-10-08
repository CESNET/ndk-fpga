//-- tbench.sv: Testbench
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

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
    reset_if                                                                                      reset(CLK);
    mfb_if #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, $clog2(SPLITTER_OUTPUTS) + META_WIDTH) mfb_rx(CLK);
    mfb_if #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)                            mfb_tx[SPLITTER_OUTPUTS](CLK);

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Define clock period
    always #(CLK_PERIOD) CLK = ~CLK;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Start of tests
    initial begin
        uvm_root m_root;
        automatic virtual mfb_if#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) v_mfb_tx[SPLITTER_OUTPUTS] = mfb_tx;

        uvm_config_db#(virtual reset_if)::set(null, "", "vif_reset", reset);
        // Configuration of database
        uvm_config_db#(virtual mfb_if #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, $clog2(SPLITTER_OUTPUTS) +META_WIDTH))::set(null, "", "vif_rx", mfb_rx);
        for (int i = 0; i < SPLITTER_OUTPUTS; i++ ) begin
            string i_string;
            i_string.itoa(i);
            uvm_config_db#(virtual mfb_if #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))::set(null, "", {"vif_tx_",i_string}, v_mfb_tx[i]);
        end

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
        .CLK        (CLK),
        .reset      (reset),
        .mfb_rx     (mfb_rx),
        .mfb_tx     (mfb_tx)
    );

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Properties

endmodule
