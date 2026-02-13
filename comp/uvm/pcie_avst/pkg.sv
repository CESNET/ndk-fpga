// pkg.sv: Package for pcie
// Copyright (C) 2024 CESNET z. s. p. o.
// Author:  Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

`ifndef PCIE_AVST_ENV_SV
`define PCIE_AVST_ENV_SV

package uvm_pcie_avst;

    `include "ndk_macros.svh"
    `include "uvm_macros.svh"
    import uvm_pkg::*;


    `include "fce.sv"
    `include "config.sv"
    `include "driver.sv"
    `include "monitor.sv"

    `include "sequence.sv"
    `include "env.sv"
    `include "root.sv"
endpackage

`endif
