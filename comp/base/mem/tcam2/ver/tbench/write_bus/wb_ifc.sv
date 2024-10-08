// wb_ifc.sv: Write Bus interface
// Copyright (C) 2020 CESNET z. s. p. o.
// Author: Tomas Hak <xhakto01@stud.fit.vutbr.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

// Write Bus RX (verification to DUT) interface
interface iWbRx #(DATA_WIDTH = 64, ADDR_WIDTH = 8) (input logic CLK, RESET);
    initial VALID_PARAMETERS : assert(DATA_WIDTH > 0 && ADDR_WIDTH > 0);

    logic [DATA_WIDTH-1 : 0] DATA = 0;
    logic [DATA_WIDTH-1 : 0] MASK = 0;
    logic [ADDR_WIDTH-1 : 0] ADDR = 0;
    logic SRC_RDY = 0;
    logic DST_RDY;

    clocking cb @(posedge CLK);
        default input #1step output #500ps;
        output DATA, MASK, ADDR, SRC_RDY;
        input DST_RDY;
    endclocking;

    clocking monitor_cb @(posedge CLK);
        default input #1step output #500ps;
        input DATA, MASK, ADDR, SRC_RDY, DST_RDY;
    endclocking: monitor_cb;

    modport dut (input DATA, MASK, ADDR, SRC_RDY, output DST_RDY);

    modport tb (clocking cb);

    modport monitor (clocking monitor_cb);

endinterface
