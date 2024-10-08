//-- dut.sv: Design under test
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import test::*;

module DUT (
    input logic     CLK,
    input logic     RST,
    mvb_if.dut_rx   mvb_rx,
    mvb_if.dut_tx   mvb_tx,
    mi_if.dut_slave config_mi
    );

    assign config_mi.ARDY = 1'b1;

    DUT_WRAPPER #(
        .MVB_ITEMS  (MVB_ITEMS),
        .LUT_DEPTH  (LUT_DEPTH),
        .LUT_WIDTH  (LUT_WIDTH),
        .LUT_ARCH   (LUT_ARCH),
        .SW_WIDTH   (SW_WIDTH),
        .META_WIDTH (META_WIDTH),
        .OUTPUT_REG (OUTPUT_REG),
        .DEVICE     (DEVICE)
    ) VHDL_DUT_U (
        .CLK             (CLK),
        .RESET           (RST),

        .RX_MVB_LUT_ADDR (mvb_rx.DATA),
        .RX_MVB_METADATA (),
        .RX_MVB_VLD      (mvb_rx.VLD),
        .RX_MVB_SRC_RDY  (mvb_rx.SRC_RDY),
        .RX_MVB_DST_RDY  (mvb_rx.DST_RDY),

        .TX_MVB_LUT_DATA (mvb_tx.DATA),
        .TX_MVB_LUT_ADDR (),
        .TX_MVB_METADATA (),
        .TX_MVB_VLD      (mvb_tx.VLD),
        .TX_MVB_SRC_RDY  (mvb_tx.SRC_RDY),
        .TX_MVB_DST_RDY  (mvb_tx.DST_RDY),
        .MI_ADDR         (config_mi.ADDR[TRUE_LUT_DEPTH+2-1 :               0]),
        .MI_SLICE        (config_mi.ADDR[ADDR_DEPTH_UP-1    : ADDR_DEPTH_DOWN]),
        .MI_DIN          (config_mi.DWR),
        .MI_BE           (config_mi.BE),
        .MI_WRITE        (config_mi.WR),
        .MI_READ         (config_mi.RD),
        .MI_DOUT         (config_mi.DRD),
        .MI_DOUT_VLD     (config_mi.DRDY)

    );


endmodule
