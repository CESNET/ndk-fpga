/*
 * file       : pkg.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: package with tests
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "base.sv"
    `include "full_speed.sv"
    `include "fifo.sv"
endpackage
