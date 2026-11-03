// pause_if.sv: Interface exposing the DUT PAUSE_REQUEST output
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
// SPDX-License-Identifier: BSD-3-Clause
//
// PAUSE_REQUEST is the top-level observable of the internal RX FIFO
// almost-full/almost-empty flags (rx_fifo_afull / rx_fifo_aempty).

interface pause_if (input logic CLK);

    logic PAUSE_REQUEST;

    clocking cb @(posedge CLK);
        input PAUSE_REQUEST;
    endclocking

    modport dut (
        input  CLK,
        output PAUSE_REQUEST
    );

    modport tb (
        input  CLK,
        input  PAUSE_REQUEST
    );

endinterface
