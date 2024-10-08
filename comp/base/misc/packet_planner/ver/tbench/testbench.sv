//-- testbench.sv: Testbench.
//-- Copyright (C) 2020 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import test_pkg::*;
`include "space_ptr_ifc.sv";

module testbench;

    logic CLK = 0;
    logic RESET;

    iMvbRx #(NUMBER_OF_PACKETS,RX_ITEM_WIDTH)       RX_STREAMS [NUMBER_OF_STREAMS](CLK, RESET);
    iMvbTx #(NUMBER_OF_PACKETS,TX_ITEM_WIDTH)       TX_STREAMS [NUMBER_OF_STREAMS](CLK, RESET);

    iMvbTx #(TX_GLOBAL_ITEMS,TX_GLOBAL_ITEM_WIDTH)  TX_GLOBAL (CLK, RESET);

    iPtr PTR_INT(CLK);

    always #(CLK_PERIOD/2) CLK = ~CLK;

    DUT DUT_U (
        .CLK            (CLK),
        .RESET          (RESET),
        .RX_STREAMS     (RX_STREAMS),
        .TX_STREAMS     (TX_STREAMS),
        .TX_GLOBAL      (TX_GLOBAL),
        .PTR_INT        (PTR_INT)
    );

    TEST TEST_U (
        .CLK                (CLK),
        .RESET              (RESET),
        .RX_STREAMS         (RX_STREAMS),
        .TX_STREAMS         (TX_STREAMS),
        .TX_GLOBAL          (TX_GLOBAL),
        .TX_STREAMS_MONITOR (TX_STREAMS),
        .TX_GLOBAL_MONITOR  (TX_GLOBAL),
        .PTR_INT            (PTR_INT)
    );

endmodule
