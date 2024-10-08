/*!
 * \file mii_ifc.sv
 * \brief General MII interface
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2016
 */
 /*
 * Copyright (C) 2016 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */



// -- MII RX Interface -------------------------------------------------------
interface iMiiRx #(int WIDTH = 0) (input logic CLK, input logic RESET);
    initial WHOLE_BYTES_ONLY : assert((WIDTH & 7) == 0);

    localparam BYTES = WIDTH >> 3;

    logic [WIDTH-1 : 0] RXD = {BYTES{8'h07}};  // Data
    logic [BYTES-1 : 0] RXC = {BYTES{1'b1}};  // Control

    clocking cb @(posedge CLK);
        default input #1step output #500ps;
        output RXD, RXC;
    endclocking;

    modport dut(input RXD, RXC);
    modport tb(clocking cb);

endinterface



// -- MII TX Interface -------------------------------------------------------
interface iMiiTx #(int WIDTH = 0) (input logic CLK, input logic RESET);
    initial WHOLE_BYTES_ONLY : assert((WIDTH & 7) == 0);

    localparam BYTES = WIDTH >> 3;

    logic [WIDTH-1 : 0] TXD;  // Data
    logic [BYTES-1 : 0] TXC;  // Control

    clocking cb @(posedge CLK);
        default input #1step output #500ps;
        input TXD, TXC;
    endclocking;

    modport dut(output TXD, TXC);
    modport tb(clocking cb);

endinterface
