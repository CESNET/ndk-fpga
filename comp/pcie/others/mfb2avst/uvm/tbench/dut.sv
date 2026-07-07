//-- dut.sv: Design under test
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import test::*;

module dut (
    input logic     CLK,
    input logic     RST,
    mfb_if.dut_rx   mfb_rx,
    avst_if.dut_tx  mfb_avst
    );

    localparam AVST_ITEMS = MFB_REGION_SIZE*MFB_BLOCK_SIZE;

    logic [MFB_REGIONS*$clog2(AVST_ITEMS)-1:0]        avst_empty;
    logic [MFB_REGIONS*AVST_ITEMS*MFB_ITEM_WIDTH-1:0] avst_data;
    logic [MFB_REGIONS*META_WIDTH-1:0]                avst_meta;

    generate
        for (genvar it = 0; it < MFB_REGIONS; it++) begin : gen_it
            assign mfb_avst.EMPTY[it] = avst_empty[(it+1)*$clog2(AVST_ITEMS)-1       -: $clog2(AVST_ITEMS)];
            assign mfb_avst.DATA[it]  = avst_data[(it+1)*AVST_ITEMS*MFB_ITEM_WIDTH-1 -: AVST_ITEMS*MFB_ITEM_WIDTH];
            assign mfb_avst.META[it]  = avst_meta[(it+1)*META_WIDTH-1                -: META_WIDTH];
        end
    endgenerate

    PCIE_MFB2AVST #(
        .REGIONS     (MFB_REGIONS),
        .REGION_SIZE (MFB_REGION_SIZE),
        .BLOCK_SIZE  (MFB_BLOCK_SIZE),
        .ITEM_WIDTH  (MFB_ITEM_WIDTH),
        .META_WIDTH  (META_WIDTH)
    ) VHDL_DUT_U (
        .CLK            (CLK),
        .RST            (RST),

        .RX_MFB_DATA    (mfb_rx.DATA),
        .RX_MFB_META    (mfb_rx.META),
        .RX_MFB_SOF     (mfb_rx.SOF),
        .RX_MFB_EOF     (mfb_rx.EOF),
        .RX_MFB_EOF_POS (mfb_rx.EOF_POS),
        .RX_MFB_SRC_RDY (mfb_rx.SRC_RDY),
        .RX_MFB_DST_RDY (mfb_rx.DST_RDY),

        .TX_AVST_DATA      (avst_data),
        .TX_AVST_META      (avst_meta),
        .TX_AVST_SOP       (mfb_avst.SOP),
        .TX_AVST_EOP       (mfb_avst.EOP),
        .TX_AVST_EMPTY     (avst_empty),
        .TX_AVST_VALID     (mfb_avst.VALID),
        .TX_AVST_READY     (mfb_avst.READY)

    );


endmodule
