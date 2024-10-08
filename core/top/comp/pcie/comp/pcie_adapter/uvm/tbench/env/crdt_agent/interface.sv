//-- interface.sv: AVST credit control interface
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause 

// Definition of AVST credit control interface.
interface crdt_if (input logic CLK);

    // ------------------------------------------------------------------------
    // Bus structure of AVST Credit control
    wire logic           INIT_DONE;
    wire logic [6-1 : 0] UPDATE;
    wire logic [2-1 : 0] CNT_PH;
    wire logic [2-1 : 0] CNT_NPH;
    wire logic [2-1 : 0] CNT_CPLH;
    wire logic [4-1 : 0] CNT_PD;
    wire logic [4-1 : 0] CNT_NPD;
    wire logic [4-1 : 0] CNT_CPLD;


    // ------------------------------------------------------------------------
    // Driver clocking block
    clocking driver_rx_cb @(posedge CLK);
        output UPDATE, CNT_PH, CNT_NPH, CNT_CPLH, CNT_PD, CNT_NPD, CNT_CPLD, INIT_DONE;
    endclocking

    clocking driver_tx_cb @(posedge CLK);
        input UPDATE, CNT_PH, CNT_NPH, CNT_CPLH, CNT_PD, CNT_NPD, CNT_CPLD;
        output INIT_DONE;
    endclocking

    // ------------------------------------------------------------------------
    // Monitor point of view (clocking block)
    clocking monitor_cb @(posedge CLK);
        input INIT_DONE, UPDATE, CNT_PH, CNT_NPH, CNT_CPLH, CNT_PD, CNT_NPD, CNT_CPLD;
    endclocking

    // ------------------------------------------------------------------------
    // Connection to DUT
    modport dut_rx(input UPDATE, CNT_PH, CNT_NPH, CNT_CPLH, CNT_PD, CNT_NPD, CNT_CPLD, INIT_DONE);
    modport dut_tx(input INIT_DONE, output UPDATE, CNT_PH, CNT_NPH, CNT_CPLH, CNT_PD, CNT_NPD, CNT_CPLD);

    // ------------------------------------------------------------------------
    // Specify wires and direction used for each connection for driver and monitor
    modport driver_rx(clocking driver_rx_cb);
    modport driver_tx(clocking driver_tx_cb);

    modport monitor(clocking monitor_cb);

endinterface
