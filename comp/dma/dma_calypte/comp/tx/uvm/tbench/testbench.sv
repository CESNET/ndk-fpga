// tbench.sv: Testbench
// Copyright (C) 2022-2024 CESNET z. s. p. o.
// Author(s): Daniel Kriz <danielkriz@cesnet.cz>
//            Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

import uvm_pkg::*;
`include "uvm_macros.svh"
import test::*;

module testbench;

    //TESTS
    typedef test::base base;
    typedef test::speed speed;

    localparam USR_MFB_META_WIDTH      = HDR_META_WIDTH + $clog2(PKT_SIZE_MAX+1) + $clog2(CHANNELS);
    localparam UPD_STOP_REQ_MVB_ITEM_W = (DATA_POINTER_WIDTH-3) + DATA_POINTER_WIDTH + 1 + 64;
    localparam RT_UPD_MVB_ITEM_W       = (DATA_POINTER_WIDTH-3) + DATA_POINTER_WIDTH + $clog2(CHANNELS);

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Signals
    logic CLK = 0;
    logic RST = 1;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Interfaces
    reset_if reset_vif (CLK);

    mfb_if #(
        .REGIONS(USR_MFB_REGIONS),
        .REGION_SIZE(USR_MFB_REGION_SIZE),
        .BLOCK_SIZE(USR_MFB_BLOCK_SIZE),
        .ITEM_WIDTH(USR_MFB_ITEM_WIDTH),
        .META_WIDTH(USR_MFB_META_WIDTH)
    ) usr_mfb_vif (
        .CLK(CLK)
    );

    mfb_if #(
        .REGIONS(PCIE_CQ_MFB_REGIONS),
        .REGION_SIZE(PCIE_CQ_MFB_REGION_SIZE),
        .BLOCK_SIZE(PCIE_CQ_MFB_BLOCK_SIZE),
        .ITEM_WIDTH(PCIE_CQ_MFB_ITEM_WIDTH),
        .META_WIDTH(sv_pcie_meta_pack::PCIE_CQ_META_WIDTH)
    ) cq_mfb_vif (
        .CLK(CLK)
    );

    mfb_if #(
        .REGIONS(PCIE_CQ_MFB_REGIONS),
        .REGION_SIZE(PCIE_CQ_MFB_REGION_SIZE),
        .BLOCK_SIZE(PCIE_CQ_MFB_BLOCK_SIZE),
        .ITEM_WIDTH(PCIE_CQ_MFB_ITEM_WIDTH),
        .META_WIDTH(sv_pcie_meta_pack::PCIE_RQ_META_WIDTH)
    ) ptr_upd_mfb_vif (
        .CLK(CLK)
    );

    mvb_if #(
        .ITEMS(1),
        .ITEM_WIDTH(UPD_STOP_REQ_MVB_ITEM_W)
    ) upd_stop_req_mvb_vif (
        .CLK(CLK)
    );

    mvb_if #(
        .ITEMS(1),
        .ITEM_WIDTH($clog2(CHANNELS))
    ) chan_start_req_mvb_vif (
        .CLK(CLK)
    );

    mvb_if #(
        .ITEMS(1),
        .ITEM_WIDTH(RT_UPD_MVB_ITEM_W)
    ) rt_upd_mvb_vif (
        .CLK(CLK)
    );

    mvb_if #(
        .ITEMS(PCIE_CQ_MFB_REGIONS),
        .ITEM_WIDTH(1)
    ) pkt_drop_meta_mvb_vif (
        .CLK(CLK)
    );

    mi_if #(
        .DATA_WIDTH(MI_WIDTH),
        .ADDR_WIDTH(MI_WIDTH)
    ) config_mi_vif (
        .CLK(CLK)
    );

    always begin
        #(CLK_PERIOD/2)
        CLK = ~CLK;
    end

    initial begin
        #(10ns)
        RST <= 0;
    end

    initial begin
        uvm_root m_root;

        $timeformat(-9, 0, " ns",10);

        // Configuration of database
        uvm_config_db#(virtual reset_if)                        ::set(null, "", "reset_vif", reset_vif);
        uvm_config_db#(virtual mfb_if #(
            .REGIONS(PCIE_CQ_MFB_REGIONS),
            .REGION_SIZE(PCIE_CQ_MFB_REGION_SIZE),
            .BLOCK_SIZE(PCIE_CQ_MFB_BLOCK_SIZE),
            .ITEM_WIDTH(PCIE_CQ_MFB_ITEM_WIDTH),
            .META_WIDTH(sv_pcie_meta_pack::PCIE_CQ_META_WIDTH)))::set(null, "", "cq_mfb_vif", cq_mfb_vif);
        uvm_config_db#(virtual mi_if  #(
            .DATA_WIDTH(MI_WIDTH),
            .ADDR_WIDTH(MI_WIDTH)))                             ::set(null, "", "config_mi_vif", config_mi_vif);
        uvm_config_db#(virtual mfb_if #(
            .REGIONS(USR_MFB_REGIONS),
            .REGION_SIZE(USR_MFB_REGION_SIZE),
            .BLOCK_SIZE(USR_MFB_BLOCK_SIZE),
            .ITEM_WIDTH(USR_MFB_ITEM_WIDTH),
            .META_WIDTH(USR_MFB_META_WIDTH)))                   ::set(null, "", "usr_mfb_vif", usr_mfb_vif);
        uvm_config_db#(virtual mfb_if #(
            .REGIONS(PCIE_CQ_MFB_REGIONS),
            .REGION_SIZE(PCIE_CQ_MFB_REGION_SIZE),
            .BLOCK_SIZE(PCIE_CQ_MFB_BLOCK_SIZE),
            .ITEM_WIDTH(PCIE_CQ_MFB_ITEM_WIDTH),
            .META_WIDTH(sv_pcie_meta_pack::PCIE_RQ_META_WIDTH)))::set(null, "", "ptr_upd_mfb_vif", ptr_upd_mfb_vif);
        uvm_config_db#(virtual mvb_if #(
            .ITEMS(1),
            .ITEM_WIDTH(UPD_STOP_REQ_MVB_ITEM_W)))              ::set(null, "", "upd_stop_req_mvb_vif",
                                                                      upd_stop_req_mvb_vif);
        uvm_config_db#(virtual mvb_if #(
            .ITEMS(1),
            .ITEM_WIDTH($clog2(CHANNELS))))                     ::set(null, "", "chan_start_req_mvb_vif",
                                                                      chan_start_req_mvb_vif);
        uvm_config_db#(virtual mvb_if #(
            .ITEMS(1),
            .ITEM_WIDTH(RT_UPD_MVB_ITEM_W)))                    ::set(null, "", "rt_upd_mvb_vif",
                                                                      rt_upd_mvb_vif);
        uvm_config_db#(virtual mvb_if #(
            .ITEMS(PCIE_CQ_MFB_REGIONS),
            .ITEM_WIDTH(1)))                                    ::set(null, "", "pkt_drop_meta_mvb_vif",
                                                                      pkt_drop_meta_mvb_vif);

        m_root = uvm_root::get();
        m_root.finish_on_completion = 0;
        m_root.set_report_id_action_hier("ILLEGALNAME",UVM_NO_ACTION);

        uvm_config_db#(int)            ::set(null, "", "recording_detail", 0);
        uvm_config_db#(uvm_bitstream_t)::set(null, "", "recording_detail", 0);

        run_test();
        $stop(2);
    end

    dut dut_i (
        .CLK                (CLK),
        .RST                (RST | reset_vif.RESET),
        .cq_mfb             (cq_mfb_vif),
        .usr_mfb            (usr_mfb_vif),
        .ptr_upd_mfb        (ptr_upd_mfb_vif),
        .upd_stop_req_mvb   (upd_stop_req_mvb_vif),
        .chan_start_req_mvb (chan_start_req_mvb_vif),
        .rt_upd_mvb         (rt_upd_mvb_vif),
        .config_mi          (config_mi_vif)
    );

    tx_dma_calypte_property #(
        .USR_MFB_REGIONS         (USR_MFB_REGIONS),
        .USR_MFB_REGION_SIZE     (USR_MFB_REGION_SIZE),
        .USR_MFB_BLOCK_SIZE      (USR_MFB_BLOCK_SIZE),
        .USR_MFB_ITEM_WIDTH      (USR_MFB_ITEM_WIDTH),
        .PCIE_CQ_MFB_REGIONS     (PCIE_CQ_MFB_REGIONS),
        .PCIE_CQ_MFB_REGION_SIZE (PCIE_CQ_MFB_REGION_SIZE),
        .PCIE_CQ_MFB_BLOCK_SIZE  (PCIE_CQ_MFB_BLOCK_SIZE),
        .PCIE_CQ_MFB_ITEM_WIDTH  (PCIE_CQ_MFB_ITEM_WIDTH),
        .USR_MFB_META_WIDTH      (USR_MFB_META_WIDTH),
        .CHANNELS                (CHANNELS),
        .UPD_STOP_REQ_MVB_ITEM_W (UPD_STOP_REQ_MVB_ITEM_W),
        .RT_UPD_MVB_ITEM_W       (RT_UPD_MVB_ITEM_W)
    ) tx_dma_calypte_property_i (
        .RESET              (RST | reset_vif.RESET),
        .cq_mfb             (cq_mfb_vif),
        .usr_mfb            (usr_mfb_vif),
        .ptr_upd_mfb        (ptr_upd_mfb_vif),
        .upd_stop_req_mvb   (upd_stop_req_mvb_vif),
        .chan_start_req_mvb (chan_start_req_mvb_vif),
        .rt_upd_mvb         (rt_upd_mvb_vif)
    );

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // GRAY BOX CONNECTION
    assign pkt_drop_meta_mvb_vif.DATA    = dut_i.vhdl_dut_i.tx_dma_chan_start_stop_ctrl_i.pkt_drop_en;
    assign pkt_drop_meta_mvb_vif.VLD     = dut_i.vhdl_dut_i.tx_dma_chan_start_stop_ctrl_i.PCIE_MFB_SOF;
    assign pkt_drop_meta_mvb_vif.SRC_RDY = dut_i.vhdl_dut_i.tx_dma_chan_start_stop_ctrl_i.PCIE_MFB_SRC_RDY;
    assign pkt_drop_meta_mvb_vif.DST_RDY = dut_i.vhdl_dut_i.tx_dma_chan_start_stop_ctrl_i.PCIE_MFB_DST_RDY;
endmodule
