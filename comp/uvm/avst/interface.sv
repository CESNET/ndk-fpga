//-- interface.sv: Mfb interface
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// Definition of mfb interface.
interface avst_if #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned ITEM_WIDTH,
    int unsigned META_WIDTH
) (
    input logic CLK
);

    initial begin
        VALID_PARAMETERS : assert(REGIONS > 0 && REGION_SIZE > 0 && ITEM_WIDTH > 0);
    end

    // ------------------------------------------------------------------------
    // Bus structure of mfb
    wire [REGION_SIZE * ITEM_WIDTH-1 : 0] DATA [REGIONS];
    wire [META_WIDTH-1 : 0]               META [REGIONS];
    wire [$clog2(REGION_SIZE) -1 : 0]     EMPTY[REGIONS];
    wire [REGIONS          -1 : 0] SOP;
    wire [REGIONS          -1 : 0] EOP;
    wire [REGIONS          -1 : 0] VALID;
    wire READY;


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
