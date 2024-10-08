//-- pkg.sv: Package for environment
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef PCIE_ADAPTER_ENV_SV
`define PCIE_ADAPTER_ENV_SV

package uvm_pcie_adapter;
    
    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "sequencer.sv"
    `include "tr_planner.sv"
    `include "monitor.sv"
    `include "sequence.sv"
    `include "generator.sv"
    `include "model_base.sv"
    `include "model_xilinx.sv"
    `include "model_intel.sv"
    `include "scoreboard_cmp.sv"
    `include "scoreboard.sv"
    `include "env.sv"

endpackage

`endif
