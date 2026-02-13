// pkg.sv: Package for pcie
// Copyright (C) 2024 CESNET z. s. p. o.
// Author:  Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

`ifndef PCIE_AXI_ENV_SV
`define PCIE_AXI_ENV_SV

package uvm_pcie_axi;

    `include "ndk_macros.svh"
    `include "uvm_macros.svh"
    import uvm_pkg::*;


    `include "config.sv"
    `include "fce.sv"
    `include "driver.sv"
    `include "monitor.sv"

    `include "sequence_cq.sv"
    `include "sequence_cc.sv"
    `include "sequence_rq.sv"
    `include "sequence_rc.sv"
    `include "env.sv"
    `include "root.sv"

endpackage

`endif
