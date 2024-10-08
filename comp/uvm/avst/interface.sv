//-- interface.sv: Mfb interface
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// Definition of mfb interface.
interface avst_if #(int unsigned REGIONS, int unsigned REGION_SIZE, int unsigned BLOCK_SIZE, int unsigned ITEM_WIDTH, int unsigned META_WIDTH) (input logic CLK);
    initial VALID_PARAMETERS : assert(REGIONS > 0 && REGION_SIZE > 0 && BLOCK_SIZE > 0 && ITEM_WIDTH > 0);

    // ------------------------------------------------------------------------
    // Parameters
    localparam WORD_WIDTH = REGIONS * REGION_SIZE * BLOCK_SIZE * ITEM_WIDTH;
    localparam META_WORD_WIDTH = REGIONS * META_WIDTH;
    localparam EMPTY_WIDTH = REGIONS * $clog2(REGION_SIZE * BLOCK_SIZE);

    // ------------------------------------------------------------------------
    // Bus structure of mfb
    wire logic [WORD_WIDTH       -1 : 0] DATA;
    wire logic [META_WORD_WIDTH  -1 : 0] META;
    wire logic [EMPTY_WIDTH      -1 : 0] EMPTY;
    wire logic [REGIONS          -1 : 0] SOP;
    wire logic [REGIONS          -1 : 0] EOP;
    wire logic [REGIONS          -1 : 0] VALID;
    wire logic READY;


    // ------------------------------------------------------------------------
    // Driver clocking block
    clocking driver_rx_cb @(posedge CLK);
        output DATA, META, EMPTY, SOP, EOP, VALID;
        input READY;
    endclocking

    clocking driver_tx_cb @(posedge CLK);
        input DATA, META, EMPTY, SOP, EOP, VALID;
        output READY;
    endclocking

    // ------------------------------------------------------------------------
    // Monitor point of view (clocking block)
    clocking monitor_cb @(posedge CLK);
        input DATA, META, EMPTY, SOP, EOP, VALID, READY;
    endclocking

    // ------------------------------------------------------------------------
    // Connection to DUT
    modport dut_rx(input DATA, META, EMPTY, SOP, EOP, VALID, output READY);
    modport dut_tx(output DATA, META, EMPTY, SOP, EOP, VALID, input READY);

    // ------------------------------------------------------------------------
    // Specify wires and direction used for each connection for driver and monitor
    modport driver_rx(clocking driver_rx_cb);
    modport driver_tx(clocking driver_tx_cb);

    modport monitor(clocking monitor_cb);

endinterface
