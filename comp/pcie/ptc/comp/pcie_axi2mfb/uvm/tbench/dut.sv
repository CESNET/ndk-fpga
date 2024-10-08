// dut.sv: Design under test
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


import test::*;

module DUT (
    input logic     CLK,
    input logic     RST,
    mfb_if.dut_tx   mfb_tx,
    axi_if.dut_rx   axi_rx
    );

    localparam SOF_POS_WIDTH = ((REGION_SIZE*REGIONS) == REGIONS) ? REGIONS : (REGIONS*$clog2(REGION_SIZE));
    logic [SOF_POS_WIDTH -1:0] sof_pos;
    assign mfb_tx.SOF_POS = sof_pos;

    PTC_PCIE_AXI2MFB #(
        .DEVICE           (DEVICE),
        .MFB_REGIONS      (REGIONS),
        .MFB_REG_SIZE     (REGION_SIZE),
        .MFB_BLOCK_SIZE   (BLOCK_SIZE),
        .MFB_ITEM_WIDTH   (ITEM_WIDTH),
        .AXI_DATA_WIDTH   (DATA_WIDTH),
        .AXI_RCUSER_WIDTH (TUSER_WIDTH)
    ) VHDL_DUT_U (
        .CLK            (CLK),
        .RESET          (RST),


        .RX_AXI_TDATA   (axi_rx.TDATA),
        .RX_AXI_TUSER   (axi_rx.TUSER),
        .RX_AXI_TVALID  (axi_rx.TVALID),
        .RX_AXI_TREADY  (axi_rx.TREADY),

        .TX_MFB_DATA    (mfb_tx.DATA),
        .TX_MFB_SOF_POS (sof_pos),
        .TX_MFB_EOF_POS (mfb_tx.EOF_POS),
        .TX_MFB_SOF     (mfb_tx.SOF),
        .TX_MFB_EOF     (mfb_tx.EOF),
        .TX_MFB_SRC_RDY (mfb_tx.SRC_RDY),
        .TX_MFB_DST_RDY (mfb_tx.DST_RDY)

    );


endmodule
