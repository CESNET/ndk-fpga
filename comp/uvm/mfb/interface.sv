//-- interface.sv: Mfb interface
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// Definition of mfb interface.
interface mfb_if #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned BLOCK_SIZE,
    int unsigned ITEM_WIDTH,
    int unsigned META_WIDTH
) (
    input logic CLK
);
    initial begin
        VALID_PARAMETERS : assert(REGIONS > 0 && REGION_SIZE > 0 && BLOCK_SIZE > 0 && ITEM_WIDTH > 0);
    end

    // ------------------------------------------------------------------------
    // Parameters
    localparam WORD_WIDTH = REGIONS * REGION_SIZE * BLOCK_SIZE * ITEM_WIDTH;
    localparam META_WORD_WIDTH = REGIONS * META_WIDTH;
    localparam SOF_POS_WIDTH = REGIONS * $clog2(REGION_SIZE);
    localparam EOF_POS_WIDTH = REGIONS * $clog2(REGION_SIZE * BLOCK_SIZE);

    // ------------------------------------------------------------------------
    // Bus structure of mfb
    wire [WORD_WIDTH       -1 : 0] DATA;
    wire [META_WORD_WIDTH  -1 : 0] META;
    wire [SOF_POS_WIDTH    -1 : 0] SOF_POS;
    wire [EOF_POS_WIDTH    -1 : 0] EOF_POS;
    wire [REGIONS          -1 : 0] SOF;
    wire [REGIONS          -1 : 0] EOF;
    wire SRC_RDY;
    wire DST_RDY;


    // ------------------------------------------------------------------------
    // Driver clocking block
    clocking driver_rx_cb @(posedge CLK);
        output DATA, META, SOF_POS, EOF_POS, SOF, EOF, SRC_RDY;
        input DST_RDY;
    endclocking

    clocking driver_tx_cb @(posedge CLK);
        input DATA, META, SOF_POS, EOF_POS, SOF, EOF, SRC_RDY;
        output DST_RDY;
    endclocking

    // ------------------------------------------------------------------------
    // Monitor point of view (clocking block)
    clocking monitor_cb @(posedge CLK);
        input DATA, META, SOF_POS, EOF_POS, SOF, EOF, SRC_RDY, DST_RDY;
    endclocking

    // ------------------------------------------------------------------------
    // Connection to DUT
    modport dut_rx(input DATA, META, SOF_POS, EOF_POS, SOF, EOF, SRC_RDY, output DST_RDY);
    modport dut_tx(output DATA, META, SOF_POS, EOF_POS, SOF, EOF, SRC_RDY, input DST_RDY);

    // ------------------------------------------------------------------------
    // Specify wires and direction used for each connection for driver and monitor
    modport driver_rx(clocking driver_rx_cb);
    modport driver_tx(clocking driver_tx_cb);

    modport monitor(clocking monitor_cb);

endinterface
