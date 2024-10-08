//-- interface.sv: Mvb interface
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// Definition of mvb interface.
interface intel_mac_seg_if #(int unsigned SEGMENTS) (input logic CLK);

    // ------------------------------------------------------------------------
    // Bus structure of mvb
    wire logic [SEGMENTS*64-1:0] DATA;
    wire logic                   VALID;
    wire logic [SEGMENTS-1:0]    INFRAME;
    wire logic [SEGMENTS*3-1:0]  EOP_EMPTY;
    wire logic [SEGMENTS-1:0]    FCS_ERROR;
    wire logic [SEGMENTS*2-1:0]  ERROR;
    wire logic [SEGMENTS*3-1:0]  STATUS_DATA;
    wire logic                   READY;

    // ------------------------------------------------------------------------
    // Driver clocking block
    clocking driver_rx_cb @(posedge CLK);
        output DATA, INFRAME, EOP_EMPTY, FCS_ERROR, ERROR, STATUS_DATA, VALID;
        input  READY;
    endclocking

    clocking driver_tx_cb @(posedge CLK);
        input DATA, INFRAME, EOP_EMPTY, FCS_ERROR, VALID;
        output READY;
    endclocking

    clocking monitor_cb @(posedge CLK);
        input DATA, INFRAME, EOP_EMPTY, FCS_ERROR, ERROR, STATUS_DATA, VALID, READY;
    endclocking

    modport dut_rx(input DATA, INFRAME, EOP_EMPTY, FCS_ERROR, ERROR, STATUS_DATA, VALID);
    modport dut_tx(output DATA, INFRAME, EOP_EMPTY, FCS_ERROR, VALID, input READY);

    // ------------------------------------------------------------------------
    // Specify wires and direction used for each connection for driver and monitor
    modport driver_rx(clocking driver_rx_cb);
    modport driver_tx(clocking driver_tx_cb);
    modport monitor(clocking monitor_cb);
endinterface

