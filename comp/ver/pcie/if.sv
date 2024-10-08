/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * SPDX-License-Identifier: BSD-3-Clause
*/

interface ipcie_rq #(DEVICE, DATA_WIDTH) (input logic CLK, RESET);
    localparam ITEM_WIDTH = 32;
    localparam AXI_USER_WIDTH = (DEVICE=="7SERIES") ? 60 : (DEVICE=="ULTRASCALE" && DATA_WIDTH == 512) ? 137 : 62;

    generate
    if (DEVICE == "ULTRASCALE" || DEVICE == "7SERIES") begin : AXI
        iAxi4STx #(DATA_WIDTH, AXI_USER_WIDTH, ITEM_WIDTH) INF(CLK, RESET);
    end else if (DEVICE == "STRATIX10" || DEVICE == "AGILEX") begin : AVALON
        avst_rx_if #(DATA_WIDTH/256)                       INF(CLK, RESET);
    end
    endgenerate


endinterface


interface ipcie_rc #(DEVICE, DATA_WIDTH) (input logic CLK, RESET);
    localparam ITEM_WIDTH     = 32;
    localparam AXI_USER_WIDTH = (DEVICE=="7SERIES") ? 75 : (DEVICE=="ULTRASCALE" && DATA_WIDTH == 512) ? 161 : 75;

    generate
    if (DEVICE == "ULTRASCALE" || DEVICE == "7SERIES") begin : AXI
        iAxi4SRx #(DATA_WIDTH, AXI_USER_WIDTH, ITEM_WIDTH) INF(CLK, RESET);
    end else if (DEVICE == "STRATIX10" || DEVICE == "AGILEX") begin : AVALON
        avst_tx_if #(DATA_WIDTH/256)                       INF(CLK, RESET);
    end
    endgenerate
endinterface
