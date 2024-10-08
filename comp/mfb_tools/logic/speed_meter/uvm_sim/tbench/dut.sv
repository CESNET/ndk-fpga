//-- dut.sv: Design under test
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import test::*;

module DUT (
    input logic     CLK,
    input logic     RST,
    mfb_if.dut_rx   mfb_rx,
    mfb_if.dut_rx   mfb_tx,
    mi_if.dut_slave config_mi
    );

    assign mfb_rx.DST_RDY = mfb_tx.DST_RDY;

    MFB_SPEED_METER_MI #(
        .REGIONS          (REGIONS),
        .REGION_SIZE      (REGION_SIZE),
        .BLOCK_SIZE       (BLOCK_SIZE),
        .ITEM_WIDTH       (ITEM_WIDTH),
        .CNT_TICKS_WIDTH  (CNT_TICKS_WIDTH),
        .CNT_BYTES_WIDTH  (CNT_BYTES_WIDTH),
        .MI_DATA_WIDTH    (MI_DATA_WIDTH),
        .MI_ADDRESS_WIDTH (MI_ADDRESS_WIDTH)
    ) VHDL_DUT_U (
        .CLK        (CLK),
        .RST        (RST),

        .MI_ADDR    (config_mi.ADDR),
        .MI_DWR     (config_mi.DWR),
        .MI_BE      (config_mi.BE),
        .MI_WR      (config_mi.WR),
        .MI_RD      (config_mi.RD),
        .MI_ARDY    (config_mi.ARDY),
        .MI_DRD     (config_mi.DRD),
        .MI_DRDY    (config_mi.DRDY),

        .RX_SOF_POS (mfb_rx.SOF_POS),
        .RX_EOF_POS (mfb_rx.EOF_POS),
        .RX_SOF     (mfb_rx.SOF),
        .RX_EOF     (mfb_rx.EOF),
        .RX_SRC_RDY (mfb_rx.SRC_RDY),
        .RX_DST_RDY (mfb_tx.DST_RDY)

    );


endmodule
