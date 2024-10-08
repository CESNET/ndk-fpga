//-- pkg.sv: Package for environment
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef CQ_MFB2AXI_ENV_SV
`define CQ_MFB2AXI_ENV_SV

package uvm_cq_mfb2axi;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "sequencer.sv"
    `include "scoreboard.sv"
    `include "env.sv"

endpackage

`endif
