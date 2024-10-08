/*!
 * \file axi4s_ifc.sv
 * \brief Multi-Frame Bus interface
 * \author Martin Spinler <spinler@cesnet.cz>
 * \date 2017
 */
 /*
 * Copyright (C) 2017 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

import math_pkg::*;

// /////////////////////////////////////////////////////////////////////////////
// Multi-Frame Bus RX (verification to DUT) interface
interface iAxi4SRx #(DATA_WIDTH = 512, USER_WIDTH = 1, ITEM_WIDTH = 8) (input logic CLK, RESET);

    logic [DATA_WIDTH-1 : 0] TDATA = 0;
    logic [USER_WIDTH-1 : 0] TUSER = 0;
    logic [DATA_WIDTH/ITEM_WIDTH-1 : 0] TKEEP = 0;
    logic TLAST = 0;
    logic TVALID = 0;
    logic TREADY;

    clocking cb @(posedge CLK);
        default input #1step output #1000ps;
        output TDATA, TUSER, TKEEP, TLAST, TVALID;
        input TREADY;
    endclocking;

    clocking monitor_cb @(posedge CLK);
        default input #1step output #1000ps;
        input TDATA, TUSER, TKEEP, TLAST, TVALID, TREADY;
    endclocking: monitor_cb;

    modport dut (input TDATA, TUSER, TKEEP, TLAST, TVALID, output TREADY);

    modport tb (clocking cb);

    modport monitor (clocking monitor_cb);

endinterface

// /////////////////////////////////////////////////////////////////////////////
// Multi-Frame Bus TX (DUT to verification) interface
interface iAxi4STx #(DATA_WIDTH = 512, USER_WIDTH = 1, ITEM_WIDTH = 8) (input logic CLK, RESET);

    logic [DATA_WIDTH-1 : 0] TDATA;
    logic [USER_WIDTH-1 : 0] TUSER;
    logic [DATA_WIDTH/ITEM_WIDTH-1 : 0] TKEEP;
    logic TLAST;
    logic TVALID;
    logic TREADY = 0;

    clocking cb @(posedge CLK);
        default input #1step output #500ps;
        input TDATA, TUSER, TKEEP, TLAST, TVALID;
        output TREADY;
    endclocking;

    clocking monitor_cb @(posedge CLK);
        default input #1step output #500ps;
        input TDATA, TUSER, TKEEP, TLAST, TVALID, TREADY;
    endclocking: monitor_cb;

    modport dut (output TDATA, TUSER, TKEEP, TLAST, TVALID, input TREADY);

    modport tb (clocking cb);

    modport monitor (clocking monitor_cb);

endinterface
