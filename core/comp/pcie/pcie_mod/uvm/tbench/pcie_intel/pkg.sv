// pkg.sv: Package for pcie convet intel to pcie
// Copyright (C) 2024 CESNET z. s. p. o.
// Author:  Radek Iša <isa@cesnet.cz> 

// SPDX-License-Identifier: BSD-3-Clause

`ifndef PCIE_INTEL_ENV_SV
`define PCIE_INTEL_ENV_SV

package uvm_pcie_intel;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    //`include "sequence.sv"

    `include "sequence.sv"

    `include "driver.sv"
    `include "monitor.sv"
    `include "env.sv"

endpackage

`endif
