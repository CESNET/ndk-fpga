//-- pkg.sv: Package for environment
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef PTC_ENV_SV
`define PTC_ENV_SV

package uvm_ptc;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "data.sv"
    `include "input_fifo.sv"

    `include "sequencer.sv"
    `include "model.sv"
    `include "scoreboard.sv"
    `include "env.sv"

endpackage

`endif
