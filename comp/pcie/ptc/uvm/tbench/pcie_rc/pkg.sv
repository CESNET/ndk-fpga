//-- pkg.sv
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef UVM_DMA_DOWN_ENV_PKG
`define UVM_DMA_DOWN_ENV_PKG

//package byte_array_mfb_env;
package uvm_pcie_rc;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "config.sv"
    `include "tr_planner.sv"
    `include "sequencer.sv"
    `include "sequence.sv"
    `include "monitor.sv"
    `include "env.sv"

endpackage

`endif
