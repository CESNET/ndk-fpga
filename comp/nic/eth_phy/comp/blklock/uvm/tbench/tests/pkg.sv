/*
 * file       : pkg.sv
 * Copyright (C) 2022 CESNET z. s. p. o.
 * description: Test pkg for Block Lock
 * date       : 2022
 * author     : Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

`ifndef BLKLOCK_TEST_SV
`define BLKLOCK_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    parameter SH_CNT_MAX = 64;
    parameter SH_INVALID_CNT_MAX = 16;
    parameter SLIP_WAIT_TIME = 32;

    parameter CLK_PERIOD = 4ns;
    parameter SLIP_PULSE = 1;

    `include "sequence.sv"
    `include "test.sv"
endpackage
`endif
