//-- tbench.sv: Testbench
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import uvm_pkg::*;
`include "uvm_macros.svh"
import test::*;

module testbench;

    //TESTS
    typedef test::base#(test::USER_REGIONS, test::USER_REGION_SIZE, test::USER_BLOCK_SIZE, test::USER_ITEM_WIDTH,
                           test::PCIE_UP_REGIONS, test::PCIE_UP_REGION_SIZE, test::PCIE_UP_BLOCK_SIZE, test::PCIE_UP_ITEM_WIDTH, test::PCIE_UP_META_WIDTH,
                           test::CHANNELS, test::PKT_SIZE_MAX, test::MI_WIDTH, test::DEVICE) base;

    typedef test::speed#(test::USER_REGIONS, test::USER_REGION_SIZE, test::USER_BLOCK_SIZE, test::USER_ITEM_WIDTH,
                            test::PCIE_UP_REGIONS, test::PCIE_UP_REGION_SIZE, test::PCIE_UP_BLOCK_SIZE, test::PCIE_UP_ITEM_WIDTH, test::PCIE_UP_META_WIDTH,
                            test::CHANNELS, test::PKT_SIZE_MAX, test::MI_WIDTH, test::DEVICE) speed;

    localparam USER_META_WIDTH = 24 + $clog2(PKT_SIZE_MAX+1) + $clog2(CHANNELS);

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Signals
    logic CLK = 0;


    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Interfaces
    reset_if                                                                                                   reset(CLK);
    mfb_if #(test::USER_REGIONS, USER_REGION_SIZE, USER_BLOCK_SIZE, USER_ITEM_WIDTH, USER_META_WIDTH)          mfb_rx(CLK);
    mfb_if #(PCIE_UP_REGIONS, PCIE_UP_REGION_SIZE, PCIE_UP_BLOCK_SIZE, PCIE_UP_ITEM_WIDTH, PCIE_UP_META_WIDTH) mfb_tx(CLK);
    mvb_if #(1, 1)                                                                                             mvb_dma(CLK);
    mi_if #(MI_WIDTH, MI_WIDTH) mi_config(CLK);

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Define clock period
    always #(CLK_PERIOD/2) CLK = ~CLK;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Start of tests
    initial begin
        uvm_root m_root;

        // Configuration of database
        uvm_config_db#(virtual reset_if)::set(null, "", "vif_reset", reset);
        uvm_config_db#(virtual mfb_if #(test::USER_REGIONS, USER_REGION_SIZE, USER_BLOCK_SIZE, USER_ITEM_WIDTH, USER_META_WIDTH))::set(null, "", "vif_rx", mfb_rx);
        uvm_config_db#(virtual mfb_if #(PCIE_UP_REGIONS, PCIE_UP_REGION_SIZE, PCIE_UP_BLOCK_SIZE, PCIE_UP_ITEM_WIDTH, PCIE_UP_META_WIDTH))::set(null, "", "vif_tx", mfb_tx);
        uvm_config_db#(virtual mvb_if #(1, 1))::set(null, "", "vif_dma", mvb_dma);
        uvm_config_db#(virtual mi_if #(MI_WIDTH, MI_WIDTH))::set(null, "", "vif_mi", mi_config);

        m_root = uvm_root::get();
        m_root.finish_on_completion = 0;
        m_root.set_report_id_action_hier("ILLEGALNAME",UVM_NO_ACTION);

        uvm_config_db#(int)            ::set(null, "", "recording_detail", 0);
        uvm_config_db#(uvm_bitstream_t)::set(null, "", "recording_detail", 0);

        $write($sformatf("Test run with seed: %d\n", $get_initial_random_seed()));

        run_test();
        $stop(2);
    end

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // DUT
    DMA_LL_DUT #(
        .DEVICE              (test::DEVICE),
        .USER_REGIONS        (test::USER_REGIONS),
        .USER_REGION_SIZE    (test::USER_REGION_SIZE   ),
        .USER_BLOCK_SIZE     (test::USER_BLOCK_SIZE    ),
        .USER_ITEM_WIDTH     (test::USER_ITEM_WIDTH    ),
        .PCIE_UP_REGIONS     (test::PCIE_UP_REGIONS    ),
        .PCIE_UP_REGION_SIZE (test::PCIE_UP_REGION_SIZE),
        .PCIE_UP_BLOCK_SIZE  (test::PCIE_UP_BLOCK_SIZE ),
        .PCIE_UP_ITEM_WIDTH  (test::PCIE_UP_ITEM_WIDTH ),
        .CHANNELS            (test::CHANNELS),
        .PKT_SIZE_MAX        (test::PKT_SIZE_MAX),
        .SW_ADDR_WIDTH       (test::SW_ADDR_WIDTH),
        .POINTER_WIDTH       (test::POINTER_WIDTH),
        .CNTRS_WIDTH         (test::CNTRS_WIDTH),
        .OPT_BUFF            (test::OPT_BUFF),
        .TRBUF_REG_EN        (test::TRBUF_REG_EN)
    )
    DUT_U (
        .CLK        (CLK),
        .RST        (reset.RESET),
        .mfb_rx     (mfb_rx),
        .mfb_tx     (mfb_tx),
        .config_mi  (mi_config)
    );


    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Properties
    DMA_LL_PROPERTY #(
        .DEVICE              (test::DEVICE),
        .USER_REGIONS        (test::USER_REGIONS),
        .USER_REGION_SIZE    (test::USER_REGION_SIZE   ),
        .USER_BLOCK_SIZE     (test::USER_BLOCK_SIZE    ),
        .USER_ITEM_WIDTH     (test::USER_ITEM_WIDTH    ),
        .PCIE_UP_REGIONS     (test::PCIE_UP_REGIONS    ),
        .PCIE_UP_REGION_SIZE (test::PCIE_UP_REGION_SIZE),
        .PCIE_UP_BLOCK_SIZE  (test::PCIE_UP_BLOCK_SIZE ),
        .PCIE_UP_ITEM_WIDTH  (test::PCIE_UP_ITEM_WIDTH ),
        .CHANNELS            (test::CHANNELS           ),
        .PKT_SIZE_MAX        (test::PKT_SIZE_MAX       )
    )
    PROPERTY_U (
        .RESET      (reset.RESET),
        .mfb_rx     (mfb_rx),
        .mfb_tx     (mfb_tx),
        .config_mi  (mi_config)
    );


    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // GRAY BOX CONNECTION
    assign mvb_dma.DATA = DUT_U.VHDL_DUT_U.rx_dma_hdr_manager_i.DMA_DISCARD;
    assign mvb_dma.VLD  = '1;
    assign mvb_dma.SRC_RDY = DUT_U.VHDL_DUT_U.rx_dma_hdr_manager_i.DMA_HDR_SRC_RDY;
    assign mvb_dma.DST_RDY = DUT_U.VHDL_DUT_U.rx_dma_hdr_manager_i.DMA_HDR_DST_RDY;

endmodule
