//-- interface.sv: AXI interface
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// Definition of AXI interface.
interface axi_if #(int unsigned DATA_WIDTH, int unsigned TUSER_WIDTH) (input logic CLK);
    // initial VALID_PARAMETERS : assert(REGIONS > 0 && REGION_SIZE > 0 && BLOCK_SIZE > 0 && ITEM_WIDTH > 0);

    // ------------------------------------------------------------------------
    // Parameters
    localparam ITEM_WIDTH   = 32;
    localparam TKEEP_WIDTH = DATA_WIDTH/ITEM_WIDTH;

    // ------------------------------------------------------------------------
    // Bus structure of AXI
    wire logic [DATA_WIDTH       -1 : 0] TDATA;
    wire logic [TUSER_WIDTH      -1 : 0] TUSER;
    wire logic [TKEEP_WIDTH      -1 : 0] TKEEP;
    wire logic                           TLAST;
    wire logic                           TVALID;
    wire logic                           TREADY;


    // ------------------------------------------------------------------------
    // Driver clocking block
    clocking driver_rx_cb @(posedge CLK);
        output TDATA, TUSER, TLAST, TKEEP, TVALID;
        input TREADY;
    endclocking

    clocking driver_tx_cb @(posedge CLK);
        input TDATA, TUSER, TLAST, TKEEP, TVALID;
        output TREADY;
    endclocking

    // ------------------------------------------------------------------------
    // Monitor point of view (clocking block)
    clocking monitor_cb @(posedge CLK);
        input TDATA, TUSER, TLAST, TKEEP, TVALID, TREADY;
    endclocking

    // ------------------------------------------------------------------------
    // Connection to DUT
    modport dut_rx(input TDATA, TUSER, TLAST, TKEEP, TVALID, output TREADY);
    modport dut_tx(output TDATA, TUSER, TLAST, TKEEP, TVALID, input TREADY);

    // ------------------------------------------------------------------------
    // Specify wires and direction used for each connection for driver and monitor
    modport driver_rx(clocking driver_rx_cb);
    modport driver_tx(clocking driver_tx_cb);

    modport monitor(clocking monitor_cb);

endinterface
