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

    localparam USR_MFB_META_WIDTH = HDR_META_WIDTH + $clog2(PKT_SIZE_MAX+1) + $clog2(CHANNELS);

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Signals
    logic CLK = 0;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Interfaces
    reset_if                                                                                                                                      reset_vif             (CLK);
    mfb_if #(USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE, USR_MFB_ITEM_WIDTH, USR_MFB_META_WIDTH)                                    usr_mfb_vif           (CLK);
    mfb_if #(PCIE_CQ_MFB_REGIONS, PCIE_CQ_MFB_REGION_SIZE, PCIE_CQ_MFB_BLOCK_SIZE, PCIE_CQ_MFB_ITEM_WIDTH, sv_pcie_meta_pack::PCIE_CQ_META_WIDTH) cq_mfb_vif            (CLK);
    // This is a bit confusing that the mvb interface is callled mfb in its name but that is because the
    // internal metainformation are transported as MFB metadata.
    mvb_if #(PCIE_CQ_MFB_REGIONS, 1)                                                                                                              internal_meta_mfb_vif (CLK);
    mi_if  #(MI_WIDTH, MI_WIDTH)                                                                                                                  config_mi_vif         (CLK);

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Define clock period
    always #(CLK_PERIOD/2) CLK = ~CLK;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Start of tests
    initial begin
        uvm_root m_root;

        $timeformat(-9, 0, " ns",10);

        // Configuration of database
        uvm_config_db#(virtual reset_if)                                                                                                                                     ::set(null, "", "reset_vif",             reset_vif);
        uvm_config_db#(virtual mfb_if #(PCIE_CQ_MFB_REGIONS, PCIE_CQ_MFB_REGION_SIZE, PCIE_CQ_MFB_BLOCK_SIZE, PCIE_CQ_MFB_ITEM_WIDTH, sv_pcie_meta_pack::PCIE_CQ_META_WIDTH))::set(null, "", "cq_mfb_vif",            cq_mfb_vif);
        uvm_config_db#(virtual mi_if  #(MI_WIDTH, MI_WIDTH))                                                                                                                 ::set(null, "", "config_mi_vif",         config_mi_vif);
        uvm_config_db#(virtual mfb_if #(USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE, USR_MFB_ITEM_WIDTH, USR_MFB_META_WIDTH))                                   ::set(null, "", "usr_mfb_vif",           usr_mfb_vif);
        uvm_config_db#(virtual mvb_if #(PCIE_CQ_MFB_REGIONS, 1))                                                                                                             ::set(null, "", "internal_meta_mfb_vif", internal_meta_mfb_vif);

        m_root = uvm_root::get();
        m_root.finish_on_completion = 0;
        m_root.set_report_id_action_hier("ILLEGALNAME",UVM_NO_ACTION);

        uvm_config_db#(int)            ::set(null, "", "recording_detail", 0);
        uvm_config_db#(uvm_bitstream_t)::set(null, "", "recording_detail", 0);

        run_test();
        $stop(2);
    end

    DUT DUT_U (
        .CLK       (CLK),
        .RST       (reset_vif.RESET),
        .cq_mfb    (cq_mfb_vif),
        .usr_mfb   (usr_mfb_vif),
        .config_mi (config_mi_vif)
    );

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Properties
    TX_DMA_CALYPTE_PROPERTY #(
        .USR_MFB_REGIONS         (USR_MFB_REGIONS),
        .USR_MFB_REGION_SIZE     (USR_MFB_REGION_SIZE),
        .USR_MFB_BLOCK_SIZE      (USR_MFB_BLOCK_SIZE),
        .USR_MFB_ITEM_WIDTH      (USR_MFB_ITEM_WIDTH),
        .PCIE_CQ_MFB_REGIONS     (PCIE_CQ_MFB_REGIONS),
        .PCIE_CQ_MFB_REGION_SIZE (PCIE_CQ_MFB_REGION_SIZE),
        .PCIE_CQ_MFB_BLOCK_SIZE  (PCIE_CQ_MFB_BLOCK_SIZE),
        .PCIE_CQ_MFB_ITEM_WIDTH  (PCIE_CQ_MFB_ITEM_WIDTH),
        .USR_MFB_META_WIDTH      (USR_MFB_META_WIDTH)
    ) tx_dma_calypte_property_i (
        .RESET                   (reset_vif.RESET),
        .cq_mfb                  (cq_mfb_vif),
        .usr_mfb                 (usr_mfb_vif)
    );

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // GRAY BOX CONNECTION
    assign internal_meta_mfb_vif.DATA    = DUT_U.VHDL_DUT_U.tx_dma_chan_start_stop_ctrl_i.pkt_drop_en;
    assign internal_meta_mfb_vif.VLD     = DUT_U.VHDL_DUT_U.tx_dma_chan_start_stop_ctrl_i.PCIE_MFB_SOF;
    assign internal_meta_mfb_vif.SRC_RDY = DUT_U.VHDL_DUT_U.tx_dma_chan_start_stop_ctrl_i.PCIE_MFB_SRC_RDY;
    assign internal_meta_mfb_vif.DST_RDY = DUT_U.VHDL_DUT_U.tx_dma_chan_start_stop_ctrl_i.PCIE_MFB_DST_RDY;
endmodule
