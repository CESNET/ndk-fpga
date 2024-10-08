/*
 * file       : pkg.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: byte_array to mii enviroment pkg
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef BYTE_ARRAY_LII_RX_PKG
`define BYTE_ARRAY_LII_RX_PKG

package uvm_byte_array_lii_rx;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "config.sv"
    `include "monitor.sv"
    `include "env.sv"

endpackage

`endif
