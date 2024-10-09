// pkg.sv: Package for pcie
// Copyright (C) 2024 CESNET z. s. p. o.
// Author:  Radek Iša <isa@cesnet.cz> 

// SPDX-License-Identifier: BSD-3-Clause

`ifndef PCIE_ENV_SV
`define PCIE_ENV_SV

package uvm_pcie;
    
    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "config.sv"

    `include "fce.sv"
    `include "header.sv"
    `include "driver.sv"
    `include "sequencer.sv"
    `include "monitor.sv"
    `include "meter.sv"
    `include "env.sv"

    `include "sequence.sv"

endpackage

`endif
