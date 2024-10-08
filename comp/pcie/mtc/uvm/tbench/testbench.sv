//-- tbench.sv: Testbench
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import uvm_pkg::*;
`include "uvm_macros.svh"
import test::*;

module testbench;

    //TESTS
    typedef test::base base;

    typedef test::speed speed;


    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Signals
    logic CLK = 0;


    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Interfaces
    reset_if                                                                                                        reset     (CLK);
    mfb_if #(MFB_REGIONS  , MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, sv_pcie_meta_pack::PCIE_CC_META_WIDTH) mfb_cc    (CLK);
    mfb_if #(MFB_REGIONS  , MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, sv_pcie_meta_pack::PCIE_CQ_META_WIDTH) mfb_cq    (CLK);
    mi_if  # (MI_DATA_WIDTH, MI_ADDR_WIDTH)                                                                         mi_config (CLK);

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Define clock period
    always #(CLK_PERIOD/2) CLK = ~CLK;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Start of tests
    initial begin
        uvm_root m_root;

        // Configuration of database
        uvm_config_db#(virtual reset_if)::set(null, "", "vif_reset", reset);
        uvm_config_db#(virtual mfb_if #(MFB_REGIONS  , MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, sv_pcie_meta_pack::PCIE_CQ_META_WIDTH))::set(null, "", "vif_cq", mfb_cq);
        uvm_config_db#(virtual mfb_if #(MFB_REGIONS  , MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, sv_pcie_meta_pack::PCIE_CC_META_WIDTH))::set(null, "", "vif_cc", mfb_cc);
        uvm_config_db#(virtual mi_if  #(MI_DATA_WIDTH, MI_ADDR_WIDTH))::set(null, "", "vif_mi", mi_config);

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
        .RST        (reset.RESET),
        .mfb_cq     (mfb_cq),
        .mfb_cc     (mfb_cc),
        .config_mi  (mi_config)
    );


    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Properties
    MTC_PROPERTY #(
        .REGIONS     (MFB_REGIONS    ),
        .REGION_SIZE (MFB_REGION_SIZE),
        .BLOCK_SIZE  (MFB_BLOCK_SIZE ),
        .ITEM_WIDTH  (MFB_ITEM_WIDTH )
    )
    PROPERTY_U (
        .RESET      (reset.RESET),
        .mfb_cq     (mfb_cq),
        .mfb_cc     (mfb_cc),
        .config_mi  (mi_config)
    );

endmodule
