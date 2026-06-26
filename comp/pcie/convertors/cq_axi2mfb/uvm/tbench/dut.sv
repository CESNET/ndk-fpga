//-- dut.sv: Design under test
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import test::*;

module dut (
    input logic     CLK,
    input logic     RST,
    axi_if.dut_rx   axi_cq,
    mfb_if.dut_tx   mfb_cq
    );

    localparam ITEM_WIDTH = 32;
    localparam AXI_ITEMS  = MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE;


    logic [((MFB_REGION_SIZE != 1) ? MFB_REGIONS*$clog2(MFB_REGION_SIZE) : MFB_REGIONS)-1 : 0] cq_sof_pos;

    assign mfb_cq.SOF_POS = cq_sof_pos;

    PCIE_CQ_AXI2MFB #(
        .MFB_REGIONS       (MFB_REGIONS),
        .MFB_REGION_SIZE   (MFB_REGION_SIZE),
        .MFB_BLOCK_SIZE    (MFB_BLOCK_SIZE),
        .MFB_ITEM_WIDTH    (ITEM_WIDTH),
        .AXI_CQUSER_WIDTH  (uvm_pcie_axi::tuser_width_get(AXI_ITEMS,   uvm_pcie_axi::AXI_CQ)),
        .AXI_DATA_WIDTH    (AXI_ITEMS*ITEM_WIDTH),
        .STRADDLING        (STRADDLING),
        .DEVICE            (DEVICE)
    ) VHDL_DUT_U (
        .CQ_AXI_DATA       (axi_cq.TDATA),
        .CQ_AXI_USER       (axi_cq.TUSER),
        .CQ_AXI_LAST       (axi_cq.TLAST),
        .CQ_AXI_KEEP       (axi_cq.TKEEP),
        .CQ_AXI_VALID      (axi_cq.TVALID),
        .CQ_AXI_READY      (axi_cq.TREADY),

        .CQ_MFB_DATA       (mfb_cq.DATA),
        .CQ_MFB_SOF        (mfb_cq.SOF),
        .CQ_MFB_EOF        (mfb_cq.EOF),
        .CQ_MFB_SOF_POS    (cq_sof_pos),
        .CQ_MFB_EOF_POS    (mfb_cq.EOF_POS),
        .CQ_MFB_SRC_RDY    (mfb_cq.SRC_RDY),
        .CQ_MFB_DST_RDY    (mfb_cq.DST_RDY),

        .CQ_TPH_PRESENT    (),
        .CQ_TPH_TYPE       (),
        .CQ_TPH_ST_TAG     (),
        .CQ_FBE            (),
        .CQ_LBE            ()
    );


endmodule
