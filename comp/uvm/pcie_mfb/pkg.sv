// pkg.sv: Package for MFB and MVB interface?
// Copyright (C) 2025 CESNET z. s. p. o.
// Author:  Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

`ifndef PCIE_MFB_ENV_SV
`define PCIE_MFB_ENV_SV

package uvm_pcie_mfb;

    `include "uvm_macros.svh"
    import uvm_pkg::*;


    `include "fce.sv"
    `include "driver.sv"
    `include "monitor.sv"

    `include "sequence.sv"
    //`include "sequence_rq.sv"
    //`include "sequence_cc.sv"
    `include "env.sv"
endpackage

`endif
