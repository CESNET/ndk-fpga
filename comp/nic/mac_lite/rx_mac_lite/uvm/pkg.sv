//-- pkg.sv: package with rx_mac_lite register model
//-- Copyright (C) 2024 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef RX_MAC_LITE_ENV_SV
`define RX_MAC_LITE_ENV_SV

package uvm_rx_mac_lite;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "registers.sv"
    `include "regmodel.sv"
endpackage
`endif

