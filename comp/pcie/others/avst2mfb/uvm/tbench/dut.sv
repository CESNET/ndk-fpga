//-- dut.sv: Design under test
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import test::*;

module DUT (
    input logic     CLK,
    input logic     RST,
    mfb_if.dut_tx   mfb_rx,
    avst_if.dut_rx  mfb_avst
    );

    assign mfb_rx.SOF_POS = '0;

    PCIE_AVST2MFB #(
        .REGIONS            (MFB_REGIONS),
        .REGION_SIZE        (MFB_REGION_SIZE),
        .BLOCK_SIZE         (MFB_BLOCK_SIZE),
        .ITEM_WIDTH         (MFB_ITEM_WIDTH),
        .META_WIDTH         (META_WIDTH),
        .AVALON_RDY_LATENCY (READY_LATENCY),
        .FIFO_DEPTH         (FIFO_DEPTH),
        .FIFO_ENABLE        (FIFO_ENABLE),
        .FIFO_RAM_TYPE      (FIFO_RAM_TYPE),
        .DEVICE             (DEVICE)
    ) VHDL_DUT_U (
        .CLK            (CLK),
        .RST            (RST),

        .RX_AVST_DATA    (mfb_avst.DATA),
        .RX_AVST_META    (mfb_avst.META),
        .RX_AVST_SOP     (mfb_avst.SOP),
        .RX_AVST_EOP     (mfb_avst.EOP),
        .RX_AVST_EMPTY   (mfb_avst.EMPTY),
        .RX_AVST_VALID   (mfb_avst.VALID),
        .RX_AVST_READY   (mfb_avst.READY),

        .TX_MFB_DATA     (mfb_rx.DATA),
        .TX_MFB_META     (mfb_rx.META),
        .TX_MFB_SOF      (mfb_rx.SOF),
        .TX_MFB_EOF      (mfb_rx.EOF),
        .TX_MFB_EOF_POS  (mfb_rx.EOF_POS),
        .TX_MFB_SRC_RDY  (mfb_rx.SRC_RDY),
        .TX_MFB_DST_RDY  (mfb_rx.DST_RDY)

    );


endmodule
