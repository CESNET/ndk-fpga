//-- pkg.sv: Package for environment
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef LOOKUP_TABLE_ENV_SV
`define LOOKUP_TABLE_ENV_SV

package uvm_lookup_table;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "regmodel.sv"
    `include "reg_sequence.sv"

    `include "sequencer.sv"
    `include "model.sv"
    `include "scoreboard.sv"
    `include "env.sv"

endpackage

`endif
