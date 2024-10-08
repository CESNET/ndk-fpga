//-- test_pkg.sv: Test Package
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


package test_pkg;

    import math_pkg::*;

    // - Parameters of DUT
    parameter DATA_WIDTH = 32;
    parameter ADDR_WIDTH = 32;
    parameter META_WIDTH = 2;

    // - Verification parameters
    parameter TRANSACTION_COUNT = 10000;

    parameter CLK_PERIOD = 10ns;
    parameter RESET_TIME = 10*CLK_PERIOD;

endpackage
