// pkg.sv: Package for PCIe environment for Intel R-Tile device
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

`ifndef PCIE_INTEL_R_TILE_ENV_SV
`define PCIE_INTEL_R_TILE_ENV_SV

package uvm_pcie_intel_r_tile;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "credit_item.sv"
    `include "credit_counter.sv"
    `include "balance_item.sv"
    `include "balance_counter.sv"
    `include "balance_splitter.sv"
    `include "valuer.sv"
    `include "transaction_approver.sv"
    `include "transaction_checker.sv"
    `include "driver.sv"
    `include "sequencer.sv"
    `include "sequence.sv"
    `include "env.sv"

endpackage

`endif
