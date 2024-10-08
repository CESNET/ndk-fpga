/*
 * file       : interface.sv
 * description: LII interface
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * Copyright (C) 2021 CESNET z. s. p. o.
*/

// Definition of LII interface.
interface lii_if_rx #(int unsigned DATA_WIDTH, logic FAST_SOF, int unsigned META_WIDTH, int unsigned SOF_WIDTH) (input logic CLK, RESET);

    // Variables
    localparam BYTES_VLD_LENGTH = $clog2(DATA_WIDTH/8)+1;

    // Bus structure of LII.
    wire logic [DATA_WIDTH-1 : 0]       DATA; // Data
    wire logic [BYTES_VLD_LENGTH-1 : 0] BYTES_VLD; // Byte valid
    wire logic [BYTES_VLD_LENGTH-1 : 0] EDB; // Byte valid, valid on EEOF cycle only.
    wire logic [SOF_WIDTH-1 : 0]        SOF;
    wire logic                          EOF; // End of frame
    wire logic                          EEOF; // End of frame
    wire logic                          RDY; // Data rdy
    wire logic                          LINK_STATUS; // Link status signalization
    wire logic                          ERR; // Decode error signalization
    wire logic                          RXSEQERR; // Sequence error
    wire logic                          RXBLKERR; // Block error signalization
    wire logic                          RXIDLE; // Signalization of idle sequence in data word
    wire logic                          RXRMTERR; // Termination error
    wire logic                          RXLOCERR; // local error
    wire logic                          CRC_OK; // Signalization of correct CRC
    wire logic                          CRC_VLD; // Signalization of valid CRC

    // Driver clocking block.
    clocking driver_cb @(posedge CLK);
        input  SOF, EOF, EEOF, BYTES_VLD, DATA, EDB, RDY, LINK_STATUS, ERR, RXSEQERR, RXBLKERR, RXIDLE, RXRMTERR, RXLOCERR, CRC_OK, CRC_VLD, RESET;
    endclocking

    // Monitor point of view (clocking block).
    clocking monitor_cb @(posedge CLK);
        input  SOF, EOF, EEOF, BYTES_VLD, DATA, EDB, LINK_STATUS, ERR, RXSEQERR, RXBLKERR, RXIDLE, RXRMTERR, RXLOCERR, CRC_OK, CRC_VLD;
        input  RESET, RDY;
    endclocking

    // Connection to DUT.
    modport dut_tx(output DATA, BYTES_VLD, SOF, EOF, EEOF, EDB, RDY, LINK_STATUS, ERR, RXSEQERR, RXBLKERR, RXIDLE, RXRMTERR, RXLOCERR, CRC_OK, CRC_VLD);
    modport dut_rx(input DATA, BYTES_VLD, SOF, EOF, EEOF, EDB, RDY, LINK_STATUS, ERR, RXSEQERR, RXBLKERR, RXIDLE, RXRMTERR, RXLOCERR, CRC_OK, CRC_VLD);

    // Specify wires and direction used for each connection for driver and monitor.
    modport driver(clocking driver_cb);

    modport monitor(clocking monitor_cb);

endinterface
