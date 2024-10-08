/*
 * interface.sv
 * Copyright (C) 2020 CESNET z. s. p. o.
 * Author(s): Radek Iša <isa@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 */


interface i_pcie_c #(DEVICE, DATA_WIDTH) (input logic CLK, RESET);

    localparam AXI_CQ_TUSER_WIDTH = (DEVICE=="7SERIES") ? 85 : (DEVICE=="ULTRASCALE" && DATA_WIDTH == 512) ? 183 : 88;
    localparam AXI_CC_TUSER_WIDTH = (DEVICE=="7SERIES") ? 33 : (DEVICE=="ULTRASCALE" && DATA_WIDTH == 512) ? 81  : 33;

    generate
    if (DEVICE == "ULTRASCALE" || DEVICE == "7SERIES") begin : AXI
        iAxi4SRx #(DATA_WIDTH, AXI_CQ_TUSER_WIDTH, 32) CQ(CLK, RESET);
        iAxi4STx #(DATA_WIDTH, AXI_CC_TUSER_WIDTH, 32) CC(CLK, RESET);
    end else if (DEVICE == "STRATIX10") begin : AVALON
        avst_tx_if #(DATA_WIDTH/256)    CQ(CLK, RESET);
        avst_rx_if #(DATA_WIDTH/256)    CC(CLK, RESET);
    end
    endgenerate
endinterface
