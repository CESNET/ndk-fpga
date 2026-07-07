//-- const.sv: Package with global constants
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef CONST
`define CONST
/*
    // dut constants
    parameter INPUT_WIDTH           = 8;
    parameter BOX_WIDTH             = 32;
    parameter BOX_CNT               = 32;
    parameter READ_PRIOR            = 0;
    parameter CLEAR_BY_READ         = 1;
    parameter CLEAR_BY_RST          = 1;
    parameter DEVICE                = "none";
*/
    // Test constants
    parameter CLK_PERIOD            = 1ns;
    parameter RESET_CLKS            = 10;
    parameter DEBUG_TIME            = 2000;

    parameter READ_OCCURENCE        = 1;
    parameter WRITE_OCCURENCE       = 100;
    parameter RAND_SEQ_REPEATS      = 5000;
/*
    parameter REQ_WIDTH             = 1 + INPUT_WIDTH + $clog2(BOX_CNT);
    parameter RESP_WIDTH            = BOX_WIDTH;
*/
/*
    typedef logic unsigned [INPUT_WIDTH     - 1 : 0] value_t;
    typedef logic unsigned [BOX_WIDTH       - 1 : 0] box_t;
    typedef logic unsigned [$clog2(BOX_CNT) - 1 : 0] addr_t;
*/
`endif
