// interface.sv: LBUS interface
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

interface lbus_if (input logic CLK);

    // --------------------- //
    // Bus structure of LBUS //
    // --------------------- //

    wire logic [4*128-1 : 0] DATA;
    wire logic [4    -1 : 0] ENA;
    wire logic [4    -1 : 0] SOP;
    wire logic [4    -1 : 0] EOP;
    wire logic [4    -1 : 0] ERR;
    wire logic [4*4  -1 : 0] MTY;
    wire logic               RDY;

    // TX driver clocking block
    clocking driver_tx_cb @(posedge CLK);
        input RDY;
        output DATA, ENA, SOP, EOP, ERR, MTY;
    endclocking

    // RX driver clocking block
    clocking driver_rx_cb @(posedge CLK);
        input DATA, ENA, SOP, EOP, ERR, MTY;
        output RDY;
    endclocking

    // Monitor clocking block
    clocking monitor_cb @(posedge CLK);
        input DATA, ENA, SOP, EOP, ERR, MTY, RDY;
    endclocking

    // TX connection to DUT
    modport dut_tx(
        input DATA, ENA, SOP, EOP, ERR, MTY,
        output RDY
    );

    // RX connection to DUT
    modport dut_rx(
        input RDY,
        output DATA, ENA, SOP, EOP, ERR, MTY
    );

    // TX driver module port
    modport driver_tx(clocking driver_tx_cb);
    // RX driver module port
    modport driver_rx(clocking driver_rx_cb);
    // Monitor module port
    modport monitor(clocking monitor_cb);

endinterface
