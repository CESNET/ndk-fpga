// dut.sv: Design under test
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


import test::*;

module DUT (
    input logic     CLK,
    input logic     RST,
    mfb_if.dut_rx   mfb_rx,
    axi_if.dut_tx   axi_tx
    );

    logic[(REGIONS*8)-1 : 0] mfb_be = '1;
    localparam SOF_POS_WIDTH = ((REGION_SIZE*REGIONS) < 2) ? 1 : (REGIONS*$clog2(REGION_SIZE));
    logic [SOF_POS_WIDTH -1:0] sof_pos;
    if ((REGIONS*$clog2(REGION_SIZE)) == 0) begin
        assign sof_pos = '0;
    end else
        assign sof_pos = mfb_rx.SOF_POS;

    PTC_MFB2PCIE_AXI #(
        .MFB_REGIONS      (REGIONS),
        .MFB_REGION_SIZE  (REGION_SIZE),
        .MFB_BLOCK_SIZE   (BLOCK_SIZE),
        .MFB_ITEM_WIDTH   (ITEM_WIDTH),
        .AXI_RQUSER_WIDTH (TUSER_WIDTH)
    ) VHDL_DUT_U (

        .RX_MFB_DATA    (mfb_rx.DATA),
        .RX_MFB_SOF_POS (sof_pos),
        .RX_MFB_EOF_POS (mfb_rx.EOF_POS),
        .RX_MFB_SOF     (mfb_rx.SOF),
        .RX_MFB_EOF     (mfb_rx.EOF),
        .RX_MFB_SRC_RDY (mfb_rx.SRC_RDY),
        .RX_MFB_DST_RDY (mfb_rx.DST_RDY),
        .RX_MFB_BE      (mfb_be),

        .RQ_DATA        (axi_tx.TDATA),
        .RQ_USER        (axi_tx.TUSER),
        .RQ_LAST        (axi_tx.TLAST),
        .RQ_KEEP        (axi_tx.TKEEP),
        .RQ_READY       (axi_tx.TREADY),
        .RQ_VALID       (axi_tx.TVALID)

    );


endmodule
