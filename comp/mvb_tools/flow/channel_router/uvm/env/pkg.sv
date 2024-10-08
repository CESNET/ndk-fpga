/*
 * file       : pkg.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: register model for application core
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef CHANNEL_ROUTER_PKG
`define CHANNEL_ROUTER_PKG

package uvm_channel_router;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "registers.sv"
    `include "block.sv"
    `include "model.sv"

endpackage

`endif
