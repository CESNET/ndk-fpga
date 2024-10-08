// interface.sv: AVST credit control interface
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

interface avst_crdt_if #(int unsigned UPDATE_CNT_WIDTH) (input logic CLK);
    // ------------------------------- //
    // Bus structure of credit control //
    // ------------------------------- //

    wire logic                          INIT;
    wire logic                          INIT_ACK;
    wire logic                          UPDATE;
    wire logic [UPDATE_CNT_WIDTH-1 : 0] UPDATE_CNT;

    // RX driver clocking block
    clocking driver_rx_cb @(posedge CLK);
        input  INIT_ACK;
        output INIT, UPDATE, UPDATE_CNT;
    endclocking

    // TX driver clocking block
    clocking driver_tx_cb @(posedge CLK);
        output INIT_ACK;
        input  INIT, UPDATE, UPDATE_CNT;
    endclocking

    // Monitor clocking block
    clocking monitor_cb @(posedge CLK);
        input INIT, INIT_ACK, UPDATE, UPDATE_CNT;
    endclocking

    // RX connection to DUT
    modport dut_rx(
        input  INIT, UPDATE, UPDATE_CNT,
        output INIT_ACK
    );

    // TX connection to DUT
    modport dut_tx(
        input  INIT_ACK,
        output INIT, UPDATE, UPDATE_CNT
    );

    // RX driver module port
    modport driver_rx(clocking driver_rx_cb);
    // TX driver module port
    modport driver_tx(clocking driver_tx_cb);

    // Monitor module port
    modport monitor(clocking monitor_cb);

endinterface
