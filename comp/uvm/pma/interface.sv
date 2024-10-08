/*
 * file       : interface.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: PMA interface
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

// Definition of MII interface.
interface pma_if #(int unsigned DATA_WIDTH) (input logic CLK, RESET);

    // Bus structure of PMA.
    wire logic [DATA_WIDTH-1 : 0] DATA; // Data
    wire logic [2-1 : 0]          HDR; // Header
    wire logic                    DATA_VLD; // Data valid
    wire logic                    HDR_VLD; // header valid
    wire logic                    BLOCK_LOCK; // Status of link

    // Driver clocking block.
    clocking driver_cb @(posedge CLK);
        output DATA, HDR, DATA_VLD, HDR_VLD, BLOCK_LOCK;
        input  RESET;
    endclocking: driver_cb

    // Monitor point of view (clocking block).
    clocking monitor_cb @(posedge CLK);
        input DATA, HDR, DATA_VLD, HDR_VLD, BLOCK_LOCK;
        input RESET;
    endclocking: monitor_cb
    // Connection to DUT.
    modport rx_dut(input DATA, HDR, DATA_VLD, HDR_VLD, BLOCK_LOCK);
    modport tx_dut(output DATA, HDR, DATA_VLD, HDR_VLD, BLOCK_LOCK);
    // Specify wires and direction used for each connection for driver and monitor.
    modport driver(clocking driver_cb);
    modport monitor(clocking monitor_cb);

endinterface
