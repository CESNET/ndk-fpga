//-- tbench.sv: Testbench
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import uvm_pkg::*;
`include "uvm_macros.svh"
import test::*;

module testbench;

        //TESTS
    typedef test::ex_test ex_test;

    typedef test::slow_dma_down_test slow_dma_down_test;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Signals
    logic CLK     = 0;
    logic CLK_DMA = 0;
    logic RST     = 0;
    logic RST_DMA = 0;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Interfaces
    mfb_if #(DMA_MFB_UP_REGIONS, MFB_UP_REG_SIZE, MFB_UP_BLOCK_SIZE, MFB_UP_ITEM_WIDTH, 0)                          UP_MFB  [DMA_PORTS](CLK_DMA);
    mvb_if #(DMA_MVB_UP_ITEMS, sv_dma_bus_pack::DMA_UPHDR_WIDTH)                                                    UP_MVB  [DMA_PORTS](CLK_DMA);

    mfb_if #(MFB_UP_REGIONS, MFB_UP_REG_SIZE, MFB_UP_BLOCK_SIZE, MFB_UP_ITEM_WIDTH, 0)                              RQ_MFB             (CLK);
    mvb_if #(MFB_UP_REGIONS, PCIE_UPHDR_WIDTH)                                                                      RQ_MVB             (CLK);
    mvb_if #(MFB_UP_REGIONS, PCIE_PREFIX_WIDTH)                                                                     RQ_PREFIX_MVB      (CLK);

    mfb_if #(MFB_DOWN_REGIONS, MFB_DOWN_REG_SIZE, MFB_DOWN_BLOCK_SIZE, MFB_DOWN_ITEM_WIDTH, PCIE_DOWNHDR_WIDTH)     RC_MFB             (CLK);
    mvb_if #(MFB_DOWN_REGIONS, PCIE_PREFIX_WIDTH)                                                                   RC_PREFIX_MVB      (CLK);

    mfb_if #(DMA_MFB_DOWN_REGIONS, MFB_DOWN_REG_SIZE, MFB_DOWN_BLOCK_SIZE, MFB_DOWN_ITEM_WIDTH, META_WIDTH)         DOWN_MFB[DMA_PORTS](CLK_DMA);
    mvb_if #(DMA_MVB_DOWN_ITEMS, sv_dma_bus_pack::DMA_DOWNHDR_WIDTH)                                                DOWN_MVB[DMA_PORTS](CLK_DMA);

    axi_if #(RQ_TDATA_WIDTH, RQ_TUSER_WIDTH)                                                                           AXI_RQ(CLK);
    axi_if #(RC_TDATA_WIDTH, RC_TUSER_WIDTH)                                                                           AXI_RC(CLK);

    reset_if                                                                                                        reset (CLK);

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Define clock period
    always #(CLK_PERIOD)     CLK     = ~CLK;
    always #(CLK_DMA_PERIOD) CLK_DMA = ~CLK_DMA;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Initial reset
    initial begin
        RST     = 1;
        #(RESET_CLKS*CLK_PERIOD)
        RST     = 0;
    end

    initial begin
        RST_DMA = 1;
        #(RESET_CLKS*CLK_DMA_PERIOD)
        RST_DMA = 0;
    end

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Start of tests
    initial begin
        uvm_root m_root;
        automatic virtual mfb_if #(DMA_MFB_UP_REGIONS, MFB_UP_REG_SIZE, MFB_UP_BLOCK_SIZE, MFB_UP_ITEM_WIDTH, 0) v_UP_MFB[DMA_PORTS]                    = UP_MFB;
        automatic virtual mvb_if #(DMA_MVB_UP_ITEMS, sv_dma_bus_pack::DMA_UPHDR_WIDTH)                                            v_UP_MVB[DMA_PORTS]   = UP_MVB;
        automatic virtual mfb_if #(DMA_MFB_DOWN_REGIONS, MFB_DOWN_REG_SIZE, MFB_DOWN_BLOCK_SIZE, MFB_DOWN_ITEM_WIDTH, META_WIDTH) v_DOWN_MFB[DMA_PORTS] = DOWN_MFB;
        automatic virtual mvb_if #(DMA_MVB_DOWN_ITEMS, sv_dma_bus_pack::DMA_DOWNHDR_WIDTH)                                        v_DOWN_MVB[DMA_PORTS] = DOWN_MVB;

        // Configuration of database
        uvm_config_db#(virtual reset_if)::set(null, "", "RESET_USER_X1", reset);
        uvm_config_db#(virtual mfb_if #(MFB_UP_REGIONS, MFB_UP_REG_SIZE, MFB_UP_BLOCK_SIZE, MFB_UP_ITEM_WIDTH, 0))::set(null, "", "vif_rq_mfb", RQ_MFB);
        uvm_config_db#(virtual mvb_if #(MFB_UP_REGIONS, PCIE_UPHDR_WIDTH))::set(null, "", "vif_rq_mvb", RQ_MVB);
        uvm_config_db#(virtual mvb_if #(MFB_UP_REGIONS, PCIE_PREFIX_WIDTH))::set(null, "", "vif_rq_prefix_mvb", RQ_PREFIX_MVB);

        uvm_config_db#(virtual mfb_if #(MFB_DOWN_REGIONS, MFB_DOWN_REG_SIZE, MFB_DOWN_BLOCK_SIZE, MFB_DOWN_ITEM_WIDTH, PCIE_DOWNHDR_WIDTH))::set(null, "", "vif_rc_mfb", RC_MFB);
        uvm_config_db#(virtual mvb_if #(MFB_DOWN_REGIONS, PCIE_PREFIX_WIDTH))::set(null, "", "vif_rc_prefix_mvb", RC_PREFIX_MVB);

        uvm_config_db#(virtual axi_if #(RQ_TDATA_WIDTH, RQ_TUSER_WIDTH))::set(null, "", "vif_rq", AXI_RQ);
        uvm_config_db#(virtual axi_if #(RC_TDATA_WIDTH, RC_TUSER_WIDTH))::set(null, "", "vif_rc", AXI_RC);

        for (int i = 0; i < DMA_PORTS; i++) begin
            string i_string;
            i_string.itoa(i);

            uvm_config_db#(virtual mfb_if #(DMA_MFB_UP_REGIONS, MFB_UP_REG_SIZE, MFB_UP_BLOCK_SIZE, MFB_UP_ITEM_WIDTH, 0))::set(null, "", {"vif_up_mfb_",i_string}, v_UP_MFB[i]);
            uvm_config_db#(virtual mvb_if #(DMA_MVB_UP_ITEMS, sv_dma_bus_pack::DMA_UPHDR_WIDTH))::set(null, "", {"vif_up_mvb_",i_string}, v_UP_MVB[i]);

            uvm_config_db#(virtual mfb_if #(DMA_MFB_DOWN_REGIONS, MFB_DOWN_REG_SIZE, MFB_DOWN_BLOCK_SIZE, MFB_DOWN_ITEM_WIDTH, META_WIDTH))::set(null, "", {"vif_down_mfb_",i_string}, v_DOWN_MFB[i]);
            uvm_config_db#(virtual mvb_if #(DMA_MVB_DOWN_ITEMS, sv_dma_bus_pack::DMA_DOWNHDR_WIDTH))::set(null, "", {"vif_down_mvb_",i_string}, v_DOWN_MVB[i]);
        end

        m_root = uvm_root::get();
        m_root.finish_on_completion = 0;
        m_root.set_report_id_action_hier("ILLEGALNAME",UVM_NO_ACTION);

        uvm_config_db#(int)            ::set(null, "", "recording_detail", 0);
        uvm_config_db#(uvm_bitstream_t)::set(null, "", "recording_detail", 0);

        run_test(TEST_NAME);
        $stop(2);
    end

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // DUT
    DUT DUT_U (
        .CLK           (CLK),
        .CLK_DMA       (CLK_DMA),
        .RST           (RST),
        .RST_DMA       (RST_DMA),
        .UP_MFB        (UP_MFB),
        .UP_MVB        (UP_MVB),
        .RQ_MFB        (RQ_MFB),
        .RQ_MVB        (RQ_MVB),
        .RQ_PREFIX_MVB (RQ_PREFIX_MVB),
        .RC_MFB        (RC_MFB),
        .RC_PREFIX_MVB (RC_PREFIX_MVB),
        .DOWN_MFB      (DOWN_MFB),
        .DOWN_MVB      (DOWN_MVB),
        .AXI_RQ        (AXI_RQ),
        .AXI_RC        (AXI_RC)
    );

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Properties
    ptc_property #(
        .DMA_MFB_UP_REGIONS   (DMA_MFB_UP_REGIONS),
        .MFB_UP_REG_SIZE      (MFB_UP_REG_SIZE),
        .MFB_UP_BLOCK_SIZE    (MFB_UP_BLOCK_SIZE),
        .MFB_UP_ITEM_WIDTH    (MFB_UP_ITEM_WIDTH),
        .DMA_MVB_UP_ITEMS     (DMA_MVB_UP_ITEMS),
        .MFB_UP_REGIONS       (MFB_UP_REGIONS),
        .PCIE_UPHDR_WIDTH     (PCIE_UPHDR_WIDTH),
        .MFB_DOWN_REGIONS     (MFB_DOWN_REGIONS),
        .MFB_DOWN_REG_SIZE    (MFB_DOWN_REG_SIZE),
        .MFB_DOWN_BLOCK_SIZE  (MFB_DOWN_BLOCK_SIZE),
        .MFB_DOWN_ITEM_WIDTH  (MFB_DOWN_ITEM_WIDTH),
        .PCIE_DOWNHDR_WIDTH   (PCIE_DOWNHDR_WIDTH),
        .DMA_MFB_DOWN_REGIONS (DMA_MFB_DOWN_REGIONS),
        .DMA_MVB_DOWN_ITEMS   (DMA_MVB_DOWN_ITEMS),
        .META_WIDTH           (META_WIDTH),
        .DMA_PORTS            (DMA_PORTS),
        .DEVICE               (DEVICE)
    )
    PROPERTY_CHECK (
        .RESET        (RST),
        .RESET_DMA    (RST_DMA),
        .up_mfb_vif   (UP_MFB),
        .up_mvb_vif   (UP_MVB),
        .rq_mfb_vif   (RQ_MFB),
        .rq_mvb_vif   (RQ_MVB),
        .down_mfb_vif (DOWN_MFB),
        .down_mvb_vif (DOWN_MVB),
        .rc_mfb_vif   (RC_MFB),
        .rq_axi_vif   (AXI_RQ),
        .rc_axi_vif   (AXI_RC)
    );

endmodule
