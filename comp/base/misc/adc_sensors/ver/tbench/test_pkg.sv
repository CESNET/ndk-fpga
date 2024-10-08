//  test_pkg.sv
//  Copyright (C) 2019 CESNET z. s. p. o.
//  Author(s): Lukas Hejcman <xhejcm01@stud.fit.vutbr.cz>
//
//  SPDX-License-Identifier: BSD-3-Clause

package test_pkg;

    // ------ CONTROL SIGNALS ------
    parameter CLK_PERIOD = 10ns;
    parameter RESET_TIME = 10*CLK_PERIOD;

    // ------ WHICH TEST TO RUN ----
    parameter TEST_STD    = 1;
    parameter TEST_BE     = 1;
    parameter TEST_RECONF = 1;

    // ------ WHAT TO TEST ---------
    parameter TEST_TEMP = 1;
    parameter TEST_VOLT = 1;

endpackage
