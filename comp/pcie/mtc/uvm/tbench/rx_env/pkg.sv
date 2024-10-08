//-- pkg.sv
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef PCIE_CQ_ENV_PKG
`define PCIE_CQ_ENV_PKG

//package uvm_pcie_cq;
package uvm_pcie_cq;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "config.sv"
    `include "sequencer.sv"
    `include "sequence.sv"
    `include "driver.sv"
    `include "env.sv"

endpackage

`endif
