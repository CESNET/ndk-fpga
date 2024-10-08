//-- testbench.sv: Testbench.
//-- Copyright (C) 2020 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import test_pkg::*;
`include "afull_ifc.sv";

module testbench;

    logic CLK = 0;
    logic RESET;

    iMvbRx #(MAX_RX_TRANS, ITEM_WIDTH)  RX_TRANS(CLK, RESET);
    iMvbTx #(MAX_RX_TRANS, ITEM_WIDTH)  RX_TRANS_MONITOR(CLK, RESET);

    iMvbTx #(MAX_TX_TRANS, ITEM_WIDTH)  TX_TRANS(CLK, RESET);

    iMvbRx #(MAX_ID_CONFS, ID_WIDTH) RX_CONFS(CLK, RESET);
    iMvbTx #(MAX_ID_CONFS, ID_WIDTH) RX_CONFS_MONITOR(CLK, RESET);

    iAFull FIFO_AFULL(CLK);

    always #(CLK_PERIOD/2) CLK = ~CLK;


    DUT DUT_U(
        .CLK                (CLK),
        .RESET              (RESET),
        .FIFO_AFULL         (FIFO_AFULL),
        .RX_TRANS           (RX_TRANS),
        .RX_TRANS_MONITOR   (RX_TRANS_MONITOR),
        .TX_TRANS           (TX_TRANS),
        .RX_CONFS           (RX_CONFS),
        .RX_CONFS_MONITOR   (RX_CONFS_MONITOR)
    );

    TEST TEST_U(
        .CLK                (CLK),
        .RESET              (RESET),
        .FIFO_AFULL         (FIFO_AFULL),
        .RX_TRANS           (RX_TRANS),
        .RX_TRANS_MONITOR   (RX_TRANS_MONITOR),
        .TX_TRANS           (TX_TRANS),
        .TX_TRANS_MONITOR   (TX_TRANS),
        .RX_CONFS           (RX_CONFS),
        .RX_CONFS_MONITOR   (RX_CONFS_MONITOR)
    );

endmodule
