//-- interface.sv: Mvb interface
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// Definition of mvb interface.
interface mvb_if #(int unsigned ITEMS, int unsigned ITEM_WIDTH) (input logic CLK);
    initial VALID_PARAMETERS : assert(ITEMS > 0 && ITEM_WIDTH > 0);

    // ------------------------------------------------------------------------
    // Parameters
    localparam WORD_WIDTH = ITEMS * ITEM_WIDTH;

    // ------------------------------------------------------------------------
    // Bus structure of mvb
    wire logic [WORD_WIDTH-1 : 0] DATA;
    wire logic [ITEMS-1 : 0] VLD;
    wire logic SRC_RDY;
    wire logic DST_RDY;

    // ------------------------------------------------------------------------
    // Driver clocking block
    clocking driver_rx_cb @(posedge CLK);
        output DATA, VLD, SRC_RDY;
        input DST_RDY;
    endclocking

    clocking driver_tx_cb @(posedge CLK);
        input DATA, VLD, SRC_RDY;
        output DST_RDY;
    endclocking

    // ------------------------------------------------------------------------
    // Monitor point of view (clocking block)
    clocking monitor_cb @(posedge CLK);
        input DATA, VLD, SRC_RDY, DST_RDY;
    endclocking

    // ------------------------------------------------------------------------
    // Connection to DUT
    modport dut_rx(input DATA, VLD, SRC_RDY, output DST_RDY);
    modport dut_tx(output DATA, VLD, SRC_RDY, input DST_RDY);

    // ------------------------------------------------------------------------
    // Specify wires and direction used for each connection for driver and monitor
    modport driver_rx(clocking driver_rx_cb);
    modport driver_tx(clocking driver_tx_cb);

    modport monitor(clocking monitor_cb);

endinterface
