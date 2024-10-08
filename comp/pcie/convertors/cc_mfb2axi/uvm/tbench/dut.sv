//-- dut.sv: Design under test
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import test::*;

module DUT (
    input logic     CLK,
    input logic     RST,
    axi_if.dut_tx   axi_cc,
    mfb_if.dut_rx   mfb_cc
    );

    logic [((MFB_REGION_SIZE != 1) ? MFB_REGIONS*$clog2(MFB_REGION_SIZE) : MFB_REGIONS)-1 : 0] cc_sof_pos;

    assign cc_sof_pos = mfb_cc.SOF_POS;

    PCIE_CC_MFB2AXI #(
        .MFB_REGIONS       (MFB_REGIONS),
        .MFB_REGION_SIZE   (MFB_REGION_SIZE),
        .MFB_BLOCK_SIZE    (MFB_BLOCK_SIZE),
        .MFB_ITEM_WIDTH    (MFB_ITEM_WIDTH),
        .AXI_CCUSER_WIDTH  (CC_TUSER_WIDTH),
        .AXI_DATA_WIDTH    (CC_TDATA_WIDTH),
        .STRADDLING        (STRADDLING)
    ) VHDL_DUT_U (
        .CC_AXI_DATA       (axi_cc.TDATA),
        .CC_AXI_USER       (axi_cc.TUSER),
        .CC_AXI_LAST       (axi_cc.TLAST),
        .CC_AXI_KEEP       (axi_cc.TKEEP),
        .CC_AXI_VALID      (axi_cc.TVALID),
        .CC_AXI_READY      (axi_cc.TREADY),

        .CC_MFB_DATA       (mfb_cc.DATA),
        .CC_MFB_SOF        (mfb_cc.SOF),
        .CC_MFB_EOF        (mfb_cc.EOF),
        .CC_MFB_SOF_POS    (cc_sof_pos),
        .CC_MFB_EOF_POS    (mfb_cc.EOF_POS),
        .CC_MFB_SRC_RDY    (mfb_cc.SRC_RDY),
        .CC_MFB_DST_RDY    (mfb_cc.DST_RDY)
    );


endmodule
