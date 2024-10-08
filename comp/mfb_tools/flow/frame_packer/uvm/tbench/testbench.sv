// tbench.sv: Testbench
// Copyright (C) 2023 CESNET z. s. p. o.
// Author:   David Beneš <xbenes52@vutbr.cz>

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
    reset_if  reset(CLK);
    mfb_if #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0) mfb_rx(CLK);
    mfb_if #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0) mfb_tx(CLK);
    mvb_if #(MVB_ITEMS, $clog2(RX_CHANNELS) + $clog2(USR_RX_PKT_SIZE_MAX+1)) mvb_rx(CLK);
    mvb_if #(MVB_ITEMS, $clog2(RX_CHANNELS) + $clog2(USR_RX_PKT_SIZE_MAX+1) + HDR_META_WIDTH + 1) mvb_tx(CLK);

    mvb_if #(1, 2) mvb_flow_ctrl[RX_CHANNELS](CLK);


    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Define clock period
    always #(CLK_PERIOD/2) CLK = ~CLK;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Start of tests
    initial begin
        automatic virtual mvb_if #(1, 2) vif_mvb_flow_ctrl[RX_CHANNELS] = mvb_flow_ctrl;
        uvm_root m_root;
        // Configuration of database
        uvm_config_db#(virtual reset_if)::set(null, "", "vif_reset", reset);
        uvm_config_db#(virtual mfb_if #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0))::set(null, "", "vif_mfb_rx", mfb_rx);
        uvm_config_db#(virtual mfb_if #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0))::set(null, "", "vif_mfb_tx", mfb_tx);
        uvm_config_db#(virtual mvb_if #(MVB_ITEMS, $clog2(RX_CHANNELS) + $clog2(USR_RX_PKT_SIZE_MAX+1)))::set(null, "", "vif_mvb_rx", mvb_rx);
        uvm_config_db#(virtual mvb_if #(MVB_ITEMS, $clog2(RX_CHANNELS) + $clog2(USR_RX_PKT_SIZE_MAX+1) + HDR_META_WIDTH + 1))::set(null, "", "vif_mvb_tx", mvb_tx);

        for (int unsigned it = 0; it < RX_CHANNELS; it++) begin
            uvm_config_db#(virtual mvb_if #(1, 2))::set(null, "", $sformatf("vif_mvb_flow_ctrl_%0d", it), vif_mvb_flow_ctrl[it]);
        end

        m_root = uvm_root::get();
        m_root.finish_on_completion = 0;
        m_root.set_report_id_action_hier("ILLEGALNAME", UVM_NO_ACTION);

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
        .mvb_rx    (mvb_rx),
        .mvb_tx    (mvb_tx)
    );

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Properties
    //framepacker_bus_properties #(
    //    .MFB_REGIONS        (MFB_REGIONS),
    //    .MFB_REGION_SIZE    (MFB_REGION_SIZE),
    //    .MFB_BLOCK_SIZE     (MFB_BLOCK_SIZE),
    //    .MFB_ITEM_WIDTH     (MFB_ITEM_WIDTH),
    //    .MFB_META_WIDTH     (MFB_META_WIDTH),
    //    .MVB_ITEMS          (MVB_ITEMS),
    //    .MVB_ITEM_WIDTH     (MVB_ITEM_WIDTH)
    //)
    //PROPERTY_CHECK (
    //    .RESET      (reset.RESET),
    //    .mfb_wr_vif (mfb_rx),
    //    .mfb_rd_vif (mfb_tx),
    //    .mvb_wr_vif (mvb_rx),
    //    .mvb_rd_vif (mvb_tx)
    //);

    //Internal connection
    generate for (genvar i = 0; i < RX_CHANNELS; i++) begin
            assign mvb_flow_ctrl[i].DATA[0]    = DUT_U.VHDL_DUT_U.ver_mod_g[i].ver_mod_i.VER_EOF;
            assign mvb_flow_ctrl[i].DATA[1]    = DUT_U.VHDL_DUT_U.ver_mod_g[i].ver_mod_i.VER_LAST;
            assign mvb_flow_ctrl[i].VLD        = DUT_U.VHDL_DUT_U.ver_mod_g[i].ver_mod_i.VER_VLD;
            assign mvb_flow_ctrl[i].SRC_RDY    = DUT_U.VHDL_DUT_U.ver_mod_g[i].ver_mod_i.VER_SRC_RDY;
            assign mvb_flow_ctrl[i].DST_RDY    = DUT_U.VHDL_DUT_U.ver_mod_g[i].ver_mod_i.VER_DST_RDY;
        end
    endgenerate
endmodule
