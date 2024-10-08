/*
 * file       : interface.sv
 * Copyright (C) 2022 CESNET z. s. p. o.
 * description: General MII interface, can be used for both RX and TX
 * date       : 2022
 * author     : Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

interface mii_if #(int unsigned CHANNELS, int unsigned WIDTH) (input logic CLK);

    initial BYTES_ONLY : assert ((WIDTH & 7) == 0);

    localparam BYTES = WIDTH >> 3;

    logic [WIDTH - 1 : 0] DATA [CHANNELS];
    logic [BYTES - 1 : 0] CONTROL [CHANNELS];
    logic CLK_EN;

    clocking driver_rx_cb @(posedge CLK);
        output DATA, CONTROL, CLK_EN;
    endclocking

    clocking driver_tx_cb @(posedge CLK);
        input DATA, CONTROL;
        output CLK_EN;
    endclocking

    clocking monitor_cb @(posedge CLK);
        input DATA, CONTROL, CLK_EN;
    endclocking

    modport dut_rx(input DATA, CONTROL, CLK_EN);
    modport dut_tx(input CLK_EN, output DATA, CONTROL);

    modport monitor(clocking monitor_cb);

    modport driver_rx(clocking driver_rx_cb);
    modport driver_tx(clocking driver_tx_cb);


endinterface: mii_if
