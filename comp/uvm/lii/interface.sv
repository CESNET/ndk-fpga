/*
 * file       : interface.sv
 * description: LII interface
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * Copyright (C) 2021 CESNET z. s. p. o.
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

// Definition of LII interface.
interface lii_if #(int unsigned DATA_WIDTH, logic FAST_SOF, int unsigned META_WIDTH, int unsigned SOF_WIDTH) (input logic CLK, RESET);

    // Variables
    localparam BYTES_VLD_LENGTH = $clog2(DATA_WIDTH/8)+1;

    // Bus structure of LII.
    wire logic [DATA_WIDTH-1 : 0]       DATA; // Data
    wire logic [BYTES_VLD_LENGTH-1 : 0] BYTES_VLD; // Byte valid
    wire logic [BYTES_VLD_LENGTH-1 : 0] EDB; // Byte valid, valid on EEOF cycle only.
    wire logic [SOF_WIDTH-1 : 0]        SOF;
    wire logic                          EOF; // End of frame
    wire logic                          RDY; // Clock enable
    wire logic                          EEOF; // Early EOF, when EEOF = 1 then next cycle EOF must be 1;
    wire logic                          LINK_STATUS; // Signalize state of ethernet link
    wire logic [META_WIDTH-1 : 0]       META; // Metadata
    wire logic                          RXDECERR; // Decode error signalization
    wire logic                          RXSEQERR; // Sequence error signalization
    wire logic                          CRCERR; // CRC error injection

    // Driver clocking block.
    clocking driver_tx_cb @(posedge CLK);
        input   SOF, EOF, BYTES_VLD, DATA, EEOF, EDB, LINK_STATUS, RESET, META, RXDECERR, RXSEQERR, CRCERR;
        output  RDY;
    endclocking

    // Driver clocking block.
    clocking driver_rx_eth_phy_cb @(posedge CLK);
        output SOF, EOF, BYTES_VLD, DATA, EEOF, EDB, RESET, META, CRCERR;
        input  RDY, LINK_STATUS, RXDECERR, RXSEQERR;
    endclocking

    // Driver clocking block.
    clocking driver_rx_cb @(posedge CLK);
        output SOF, EOF, BYTES_VLD, DATA, EEOF, EDB, LINK_STATUS, META, RXDECERR, RXSEQERR, CRCERR;
        input  RDY, RESET;
    endclocking

    // Monitor point of view (clocking block).
    clocking monitor_cb @(posedge CLK);
        input  DATA, SOF, EOF, BYTES_VLD, EEOF, EDB, LINK_STATUS, META, RXDECERR, RXSEQERR, CRCERR;
        input  RESET, RDY;
    endclocking

    // Connection to DUT.
    modport dut_tx(output DATA, BYTES_VLD, SOF, EOF, EEOF, EDB, LINK_STATUS, META, RXDECERR, RXSEQERR, CRCERR, input RDY);
    modport dut_rx_eth_phy(input DATA, BYTES_VLD, SOF, EOF, EEOF, EDB, META, CRCERR, output RDY, LINK_STATUS, RXDECERR, RXSEQERR);
    modport dut_rx(input DATA, BYTES_VLD, SOF, EOF, EEOF, EDB, LINK_STATUS, META, RXDECERR, RXSEQERR, CRCERR, output RDY);

    // Specify wires and direction used for each connection for driver and monitor.
    modport driver_tx(clocking driver_tx_cb);
    modport driver_tx_eth_phy(clocking driver_rx_eth_phy_cb);
    modport driver_rx(clocking driver_rx_cb);

    modport monitor(clocking monitor_cb);

endinterface
