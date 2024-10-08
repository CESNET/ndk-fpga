/*!
 * \file dut.sv
 * \brief Design Under Test
 * \author Daniel Kondys <xkondy00@vutbr.cz>
 * \date 2020
 */
 /*
 * Copyright (C) 2020 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

import test_pkg::*;

module DUT (
    input logic CLK,
    input logic RESET,
    iMi.slave   RX,
    iMi.master  TX[PORTS]
);

    logic [DATA_WIDTH-1:0] dwr[PORTS-1:0];
    logic [META_WIDTH-1:0] mwr[PORTS-1:0];
    logic [ADDR_WIDTH-1:0] addr[PORTS-1:0];
    logic [DATA_WIDTH/8-1:0] be[PORTS-1:0];
    logic [PORTS-1:0] rd;
    logic [PORTS-1:0] wr;
    logic [PORTS-1:0] ardy;
    logic [DATA_WIDTH-1:0] drd[PORTS-1:0];
    logic [PORTS-1:0] drdy;

    MI_SPLITTER_PLUS_GEN_WRAPPER #(
        .ADDR_WIDTH    (ADDR_WIDTH)  ,
        .DATA_WIDTH    (DATA_WIDTH)  ,
        .META_WIDTH    (META_WIDTH)  ,
        .PORTS         (PORTS)       ,
        .PIPE_OUT      (PIPE_OUT)    ,
        .ADDR_MASK     (ADDR_MASK)   ,
        .ADDR_BASES    (ADDR_BASES)  ,
        .ADDR_BASE     (ADDR_BASE)   ,
        .PORT_MAPPING  (PORT_MAPPING),
        .DEVICE        (DEVICE)
    ) VHDL_DUT_U (
        .CLK        (CLK)        ,
        .RESET      (RESET)      ,

        .RX_DWR     (RX.DWR)     ,
        .RX_MWR     (RX.MWR)     ,
        .RX_ADDR    (RX.ADDR)    ,
        .RX_BE      (RX.BE)      ,
        .RX_RD      (RX.RD)      ,
        .RX_WR      (RX.WR)      ,
        .RX_ARDY    (RX.ARDY)    ,
        .RX_DRD     (RX.DRD)     ,
        .RX_DRDY    (RX.DRDY)    ,

        .TX_DWR     (dwr)        ,
        .TX_MWR     (mwr)        ,
        .TX_ADDR    (addr)       ,
        .TX_BE      (be)         ,
        .TX_RD      (rd)         ,
        .TX_WR      (wr)         ,
        .TX_ARDY    (ardy)       ,
        .TX_DRD     (drd)        ,
        .TX_DRDY    (drdy)
    );

    generate
        for (genvar i = 0; i < PORTS; i++) begin
            assign TX[i].DWR  = dwr[i];
            assign TX[i].MWR  = mwr[i];
            assign TX[i].ADDR = addr[i];
            assign TX[i].BE   = be[i];
            assign TX[i].RD   = rd[i];
            assign TX[i].WR   = wr[i];
            assign ardy[i]    = TX[i].ARDY;
            assign drd[i]     = TX[i].DRD;
            assign drdy[i]    = TX[i].DRDY;
        end
    endgenerate

endmodule
