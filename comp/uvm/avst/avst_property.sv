//-- avst_property.sv: Properties for avst bus
//-- Copyright (C) 2025 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef AVST_PROPERTY
`define AVST_PROPERTY


`include "uvm_macros.svh"
import uvm_pkg::*;

`include "avst_pcie_propert.sv"

module avst_property #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned ITEM_WIDTH,
    int unsigned META_WIDTH
)(
    input RESET,
    mfb_if vif
);


endmodule

`endif
