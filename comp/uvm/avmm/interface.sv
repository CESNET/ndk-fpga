// interface.sv: AVMM interface
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

interface avmm_if #(int unsigned ADDRESS_WIDTH, int unsigned DATA_WIDTH, int unsigned BURST_WIDTH) (input logic CLK);
    initial VALID_PARAMETERS : assert(ADDRESS_WIDTH > 0 && DATA_WIDTH > 0 && BURST_WIDTH > 0);

    // Bus structure of AVMM
    wire logic                       READY;
    wire logic                       READ;
    wire logic                       WRITE;
    wire logic [ADDRESS_WIDTH-1 : 0] ADDRESS;
    wire logic [DATA_WIDTH   -1 : 0] READDATA;
    wire logic                       READDATAVALID;
    wire logic [DATA_WIDTH   -1 : 0] WRITEDATA;
    wire logic [BURST_WIDTH  -1 : 0] BURSTCOUNT;

    // ---------------------- //
    // Driver clocking blocks //
    // ---------------------- //

    clocking driver_slave_cb @(posedge CLK);
        output READ, WRITE, ADDRESS, WRITEDATA, BURSTCOUNT;
        input READY, READDATA, READDATAVALID;
    endclocking

    clocking driver_master_cb @(posedge CLK);
        input READ, WRITE, ADDRESS, WRITEDATA, BURSTCOUNT;
        output READY, READDATA, READDATAVALID;
    endclocking

    // Monitor point of view (clocking block)
    clocking monitor_cb @(posedge CLK);
        input READY, READ, WRITE, ADDRESS, READDATA, READDATAVALID, WRITEDATA, BURSTCOUNT;
    endclocking

    // Connection to DUT
    modport dut_slave (input READ, WRITE, ADDRESS, WRITEDATA, BURSTCOUNT, output READY, READDATA, READDATAVALID);
    modport dut_master (output READ, WRITE, ADDRESS, WRITEDATA, BURSTCOUNT, input READY, READDATA, READDATAVALID);

    // Specifies wires and direction used for each connection for driver and monitor
    modport driver_slave (clocking driver_slave_cb);
    modport driver_master (clocking driver_master_cb);

    modport monitor (clocking monitor_cb);

endinterface
