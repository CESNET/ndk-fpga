//-- tbench.sv: Testbench
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import uvm_pkg::*;
`include "uvm_macros.svh"
import test::*;

module testbench;

    localparam PTR_UPD_REQ_MVB_ITEM_W = 2*POINTER_WIDTH + 1 + SW_ADDR_WIDTH;

    //TESTS
    typedef test::base#(test::USR_MFB_REGIONS, test::USR_MFB_REGION_SIZE, test::USR_MFB_BLOCK_SIZE, test::USR_MFB_ITEM_WIDTH,
                        test::PCIE_RQ_REGIONS, test::PCIE_RQ_REGION_SIZE, test::PCIE_RQ_BLOCK_SIZE, test::PCIE_RQ_ITEM_WIDTH, test::PCIE_RQ_META_WIDTH,
                        test::CHANNELS, test::PKT_SIZE_MAX, test::MI_WIDTH, test::DEVICE, POINTER_WIDTH, SW_ADDR_WIDTH) base;

    typedef test::speed#(test::USR_MFB_REGIONS, test::USR_MFB_REGION_SIZE, test::USR_MFB_BLOCK_SIZE, test::USR_MFB_ITEM_WIDTH,
                         test::PCIE_RQ_REGIONS, test::PCIE_RQ_REGION_SIZE, test::PCIE_RQ_BLOCK_SIZE, test::PCIE_RQ_ITEM_WIDTH, test::PCIE_RQ_META_WIDTH,
                         test::CHANNELS, test::PKT_SIZE_MAX, test::MI_WIDTH, test::DEVICE, POINTER_WIDTH, SW_ADDR_WIDTH) speed;

    localparam USR_MFB_META_WIDTH = 24 + $clog2(PKT_SIZE_MAX+1) + $clog2(CHANNELS);

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Signals
    logic CLK = 0;
    logic RST = 1;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Interfaces
    reset_if                                                                                                   reset(CLK);
    mfb_if #(USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE, USR_MFB_ITEM_WIDTH, USR_MFB_META_WIDTH) usr_mfb(CLK);
    mfb_if #(PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE, PCIE_RQ_BLOCK_SIZE, PCIE_RQ_ITEM_WIDTH, PCIE_RQ_META_WIDTH) pcie_rq_mfb(CLK);
    mfb_if #(PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE, PCIE_RQ_BLOCK_SIZE, PCIE_RQ_ITEM_WIDTH, PCIE_RQ_META_WIDTH) ptr_upd_mfb(CLK);
    mvb_if #(1, PTR_UPD_REQ_MVB_ITEM_W)                                                                        ptr_upd_req_mvb(CLK);
    mvb_if #(1, 1)                                                                                             pkt_disc_mvb(CLK);
    mi_if #(MI_WIDTH, MI_WIDTH)                                                                                mi_config(CLK);

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Define clock period
    always #(CLK_PERIOD/2) CLK = ~CLK;
    initial #(10ns) RST <= 0;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Start of tests
    initial begin
        uvm_root m_root;

        // Configuration of database
        uvm_config_db#(virtual reset_if)::set(null, "", "reset_vif", reset);
        uvm_config_db#(virtual mfb_if #(test::USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE, USR_MFB_ITEM_WIDTH, USR_MFB_META_WIDTH))::set(null, "", "usr_mfb_vif", usr_mfb);
        uvm_config_db#(virtual mfb_if #(PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE, PCIE_RQ_BLOCK_SIZE, PCIE_RQ_ITEM_WIDTH, PCIE_RQ_META_WIDTH))::set(null, "", "pcie_rq_mfb_vif", pcie_rq_mfb);
        uvm_config_db#(virtual mfb_if #(PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE, PCIE_RQ_BLOCK_SIZE, PCIE_RQ_ITEM_WIDTH, PCIE_RQ_META_WIDTH))::set(null, "", "ptr_upd_mfb_vif", ptr_upd_mfb);
        uvm_config_db#(virtual mvb_if #(1, PTR_UPD_REQ_MVB_ITEM_W))::set(null, "", "ptr_upd_req_mvb_vif", ptr_upd_req_mvb);
        uvm_config_db#(virtual mvb_if #(1, 1))::set(null, "", "pkt_disc_mvb_vif", pkt_disc_mvb);
        uvm_config_db#(virtual mi_if #(MI_WIDTH, MI_WIDTH))::set(null, "", "config_mi_vif", mi_config);

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
        .USR_MFB_REGIONS     (test::USR_MFB_REGIONS),
        .USR_MFB_REGION_SIZE (test::USR_MFB_REGION_SIZE),
        .USR_MFB_BLOCK_SIZE  (test::USR_MFB_BLOCK_SIZE ),
        .USR_MFB_ITEM_WIDTH  (test::USR_MFB_ITEM_WIDTH ),
        .PCIE_RQ_REGIONS     (test::PCIE_RQ_REGIONS    ),
        .PCIE_RQ_REGION_SIZE (test::PCIE_RQ_REGION_SIZE),
        .PCIE_RQ_BLOCK_SIZE  (test::PCIE_RQ_BLOCK_SIZE ),
        .PCIE_RQ_ITEM_WIDTH  (test::PCIE_RQ_ITEM_WIDTH ),
        .CHANNELS            (test::CHANNELS),
        .PKT_SIZE_MAX        (test::PKT_SIZE_MAX),
        .SW_ADDR_WIDTH       (test::SW_ADDR_WIDTH),
        .POINTER_WIDTH       (test::POINTER_WIDTH),
        .CNTRS_WIDTH         (test::CNTRS_WIDTH),
        .TRBUF_REG_EN        (test::TRBUF_REG_EN),
        .PERF_CNTR_EN        (test::PERF_CNTR_EN)
    )
    DUT_U (
        .CLK             (CLK),
        .RST             (RST | reset.RESET),
        .usr_mfb         (usr_mfb),
        .pcie_rq_mfb     (pcie_rq_mfb),
        .ptr_upd_mfb     (ptr_upd_mfb),
        .ptr_upd_req_mvb (ptr_upd_req_mvb),
        .config_mi       (mi_config)
    );


    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Properties
    DMA_LL_PROPERTY #(
        .DEVICE              (test::DEVICE),
        .USR_MFB_REGIONS     (test::USR_MFB_REGIONS),
        .USR_MFB_REGION_SIZE (test::USR_MFB_REGION_SIZE),
        .USR_MFB_BLOCK_SIZE  (test::USR_MFB_BLOCK_SIZE ),
        .USR_MFB_ITEM_WIDTH  (test::USR_MFB_ITEM_WIDTH ),
        .PCIE_RQ_REGIONS     (test::PCIE_RQ_REGIONS    ),
        .PCIE_RQ_REGION_SIZE (test::PCIE_RQ_REGION_SIZE),
        .PCIE_RQ_BLOCK_SIZE  (test::PCIE_RQ_BLOCK_SIZE ),
        .PCIE_RQ_ITEM_WIDTH  (test::PCIE_RQ_ITEM_WIDTH ),
        .CHANNELS            (test::CHANNELS           ),
        .PKT_SIZE_MAX        (test::PKT_SIZE_MAX       )
    )
    PROPERTY_U (
        .RESET       (RST | reset.RESET),
        .usr_mfb     (usr_mfb),
        .pcie_rq_mfb (pcie_rq_mfb),
        .ptr_upd_mfb (ptr_upd_mfb),
        .config_mi   (mi_config)
    );


    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // GRAY BOX CONNECTION
    assign pkt_disc_mvb.DATA = DUT_U.VHDL_DUT_U.rx_dma_hdr_manager_i.DMA_DISCARD;
    assign pkt_disc_mvb.VLD  = '1;
    assign pkt_disc_mvb.SRC_RDY = DUT_U.VHDL_DUT_U.rx_dma_hdr_manager_i.DMA_HDR_SRC_RDY;
    assign pkt_disc_mvb.DST_RDY = DUT_U.VHDL_DUT_U.rx_dma_hdr_manager_i.DMA_HDR_DST_RDY;

endmodule
