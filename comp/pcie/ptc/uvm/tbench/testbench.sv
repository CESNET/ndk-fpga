//-- tbench.sv: Testbench
//-- Copyright (C) 2025 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import uvm_pkg::*;
`include "uvm_macros.svh"
import test::*;

module testbench;

        //TESTS
    //typedef test::ex_test ex_test;
    //typedef test::slow_dma_down_test slow_dma_down_test;
    localparam IS_INTEL = (DEVICE == "STRATIX10" ||  DEVICE == "AGILEX") ? 1'b1 : 1'b0;
    localparam RQ_AXI_ITEMS = (IS_INTEL == 0) ? MFB_UP_REGIONS*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE       : 16;
    localparam RC_AXI_ITEMS = (IS_INTEL == 0) ? MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE : 16;
    localparam ITEM_WIDTH = 32;
    localparam PCIE_DOWNHDR_WIDTH = sv_pcie_meta_pack::PCIE_RC_META_WIDTH;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Signals
    logic CLK     = 0;
    logic CLK_DMA = 0;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Interfaces
    mfb_if #(DMA_MFB_UP_REGIONS, MFB_UP_REG_SIZE, MFB_UP_BLOCK_SIZE, ITEM_WIDTH, 0)                        DMA_RX_MFB  [DMA_PORTS](CLK_DMA);
    mvb_if #(DMA_MVB_UP_ITEMS, sv_dma_bus_pack::DMA_UPHDR_WIDTH)                                           DMA_RX_MVB  [DMA_PORTS](CLK_DMA);

    localparam RQ_META_WIDTH = uvm_pcie_mfb::meta_width_get(uvm_pcie_mfb::MFB_RQ, uvm_pcie_mfb::DEV_INTEL);
    mfb_if #(MFB_UP_REGIONS, MFB_UP_REG_SIZE, MFB_UP_BLOCK_SIZE, ITEM_WIDTH, 0)  RQ_MFB(CLK);
    mvb_if #(MFB_UP_REGIONS, RQ_META_WIDTH)                                      RQ_MVB(CLK);

    localparam RC_META_WIDTH = uvm_pcie_mfb::meta_width_get(uvm_pcie_mfb::MFB_RC, uvm_pcie_mfb::DEV_INTEL);
    mfb_if #(MFB_DOWN_REGIONS, MFB_DOWN_REG_SIZE, MFB_DOWN_BLOCK_SIZE, ITEM_WIDTH, RC_META_WIDTH)          RC_MFB(CLK);

    mfb_if #(DMA_MFB_DOWN_REGIONS, MFB_DOWN_REG_SIZE, MFB_DOWN_BLOCK_SIZE, ITEM_WIDTH, 0)                  DMA_TX_MFB[DMA_PORTS](CLK_DMA);
    mvb_if #(DMA_MVB_DOWN_ITEMS, sv_dma_bus_pack::DMA_DOWNHDR_WIDTH)                                       DMA_TX_MVB[DMA_PORTS](CLK_DMA);

    axi_if #(RQ_AXI_ITEMS, 32,uvm_pcie_axi::tuser_width_get(RQ_AXI_ITEMS, uvm_pcie_axi::AXI_RQ)) AXI_RQ(CLK);
    axi_if #(RC_AXI_ITEMS, 32,uvm_pcie_axi::tuser_width_get(RC_AXI_ITEMS, uvm_pcie_axi::AXI_RC)) AXI_RC(CLK);

    reset_if RST_DMA(CLK_DMA);
    pullup(RST_DMA.RESET);
    reset_if RST    (CLK);
    pullup(RST.RESET);

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // PROBE
    bind PCIE_TRANSACTION_CTRL : $root.testbench.DUT_U.VHDL_DUT_U.ptc_i probe_inf #(MVB_UP_ITEMS*(1 + PCIE_TAG_WIDTH + sv_dma_bus_pack::DMA_UPHDR_WIDTH)) probe_tag(
                    {tagm_mvb_out_src_rdy & tagm_mvb_out_dst_rdy}, {tagm_mvb_out, tagm_mvb_out_tag, tagm_mvb_out_vld}, CLK);



    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Define clock period
    always #(CLK_PERIOD)     CLK     = ~CLK;
    always #(CLK_DMA_PERIOD) CLK_DMA = ~CLK_DMA;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Start of tests
    initial begin
        uvm_root m_root;
        automatic virtual mfb_if #(DMA_MFB_UP_REGIONS, MFB_UP_REG_SIZE, MFB_UP_BLOCK_SIZE, ITEM_WIDTH, 0) v_UP_MFB[DMA_PORTS]  = DMA_RX_MFB;
        automatic virtual mvb_if #(DMA_MVB_UP_ITEMS, sv_dma_bus_pack::DMA_UPHDR_WIDTH)                    v_UP_MVB[DMA_PORTS]  = DMA_RX_MVB;
        automatic virtual mfb_if #(DMA_MFB_DOWN_REGIONS, MFB_DOWN_REG_SIZE, MFB_DOWN_BLOCK_SIZE, ITEM_WIDTH, 0) v_DOWN_MFB[DMA_PORTS] = DMA_TX_MFB;
        automatic virtual mvb_if #(DMA_MVB_DOWN_ITEMS, sv_dma_bus_pack::DMA_DOWNHDR_WIDTH)                                        v_DOWN_MVB[DMA_PORTS] = DMA_TX_MVB;

        // Configuration of database
        uvm_config_db#(virtual reset_if)::set(null, "", "vif_reset", RST);
        uvm_config_db#(virtual reset_if)::set(null, "", "vif_reset_dma", RST_DMA);

        uvm_config_db#(virtual mfb_if #(MFB_UP_REGIONS, MFB_UP_REG_SIZE, MFB_UP_BLOCK_SIZE, ITEM_WIDTH, 0))::set(null, "", "vif_pcie_rq_mfb", RQ_MFB);
        uvm_config_db#(virtual mvb_if #(MFB_UP_REGIONS, RQ_META_WIDTH))::set(null, "", "vif_pcie_rq_mvb", RQ_MVB);

        uvm_config_db#(virtual mfb_if #(MFB_DOWN_REGIONS, MFB_DOWN_REG_SIZE, MFB_DOWN_BLOCK_SIZE, ITEM_WIDTH, RC_META_WIDTH))::set(null, "", "vif_pcie_rc_mfb", RC_MFB);

        uvm_config_db#(virtual axi_if #(RQ_AXI_ITEMS, 32, uvm_pcie_axi::tuser_width_get(RQ_AXI_ITEMS, uvm_pcie_axi::AXI_RQ)))::set(null, "", "vif_pcie_rq_axi", AXI_RQ);
        uvm_config_db#(virtual axi_if #(RC_AXI_ITEMS, 32, uvm_pcie_axi::tuser_width_get(RC_AXI_ITEMS, uvm_pcie_axi::AXI_RC)))::set(null, "", "vif_pcie_rc_axi", AXI_RC);

        for (int i = 0; i < DMA_PORTS; i++) begin
            string i_string;
            i_string.itoa(i);

            uvm_config_db#(virtual mfb_if #(DMA_MFB_UP_REGIONS, MFB_UP_REG_SIZE, MFB_UP_BLOCK_SIZE, ITEM_WIDTH, 0))::set(null, "", {"vif_dma_",i_string, "_rq_mfb"}, v_UP_MFB[i]);
            uvm_config_db#(virtual mvb_if #(DMA_MVB_UP_ITEMS, sv_dma_bus_pack::DMA_UPHDR_WIDTH))::set(null, "", {"vif_dma_",i_string, "_rq_mvb"}, v_UP_MVB[i]);

            uvm_config_db#(virtual mfb_if #(DMA_MFB_DOWN_REGIONS, MFB_DOWN_REG_SIZE, MFB_DOWN_BLOCK_SIZE, ITEM_WIDTH, 0))::set(null, "", {"vif_dma_",i_string, "_rc_mfb"}, v_DOWN_MFB[i]);
            uvm_config_db#(virtual mvb_if #(DMA_MVB_DOWN_ITEMS, sv_dma_bus_pack::DMA_DOWNHDR_WIDTH))::set(null, "", {"vif_dma_",i_string, "_rc_mvb"}, v_DOWN_MVB[i]);
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
        .CLK           (CLK),
        .CLK_DMA       (CLK_DMA),
        .RST           (RST.RESET     == 1'b1 ? 1'b1 : 1'b0),
        .RST_DMA       (RST_DMA.RESET == 1'b1 ? 1'b1 : 1'b0),
        .DMA_RX_MFB    (DMA_RX_MFB),
        .DMA_RX_MVB    (DMA_RX_MVB),
        .RQ_MFB        (RQ_MFB),
        .RQ_MVB        (RQ_MVB),
        .RC_MFB        (RC_MFB),
        .DMA_TX_MFB      (DMA_TX_MFB),
        .DMA_TX_MVB      (DMA_TX_MVB),
        .AXI_RQ        (AXI_RQ),
        .AXI_RC        (AXI_RC)
    );

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Properties
    ptc_property #(
        .DMA_MFB_UP_REGIONS   (DMA_MFB_UP_REGIONS),
        .MFB_UP_REG_SIZE      (MFB_UP_REG_SIZE),
        .MFB_UP_BLOCK_SIZE    (MFB_UP_BLOCK_SIZE),
        .MFB_UP_ITEM_WIDTH    (ITEM_WIDTH),
        .DMA_MVB_UP_ITEMS     (DMA_MVB_UP_ITEMS),
        .MFB_UP_REGIONS       (MFB_UP_REGIONS),
        .PCIE_UP_META_WIDTH   (sv_pcie_meta_pack::PCIE_RQ_META_WIDTH),
        .MFB_DOWN_REGIONS     (MFB_DOWN_REGIONS),
        .MFB_DOWN_REG_SIZE    (MFB_DOWN_REG_SIZE),
        .MFB_DOWN_BLOCK_SIZE  (MFB_DOWN_BLOCK_SIZE),
        .MFB_DOWN_ITEM_WIDTH  (ITEM_WIDTH),
        .PCIE_DOWN_META_WIDTH (sv_pcie_meta_pack::PCIE_RC_META_WIDTH),
        .DMA_MFB_DOWN_REGIONS (DMA_MFB_DOWN_REGIONS),
        .DMA_MVB_DOWN_ITEMS   (DMA_MVB_DOWN_ITEMS),
        .DMA_PORTS            (DMA_PORTS),
        .DEVICE               (DEVICE)
    )
    PROPERTY_CHECK (
        .RESET        (RST.RESET),
        .RESET_DMA    (RST_DMA.RESET),
        .up_mfb_vif   (DMA_RX_MFB),
        .up_mvb_vif   (DMA_RX_MVB),
        .rq_mfb_vif   (RQ_MFB),
        .rq_mvb_vif   (RQ_MVB),
        .down_mfb_vif (DMA_TX_MFB),
        .down_mvb_vif (DMA_TX_MVB),
        .rc_mfb_vif   (RC_MFB),
        .rq_axi_vif   (AXI_RQ),
        .rc_axi_vif   (AXI_RC)
    );

endmodule
