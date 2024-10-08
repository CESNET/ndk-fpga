//-- pkg.sv: Package for environment
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef MERGE_ITEMS_ENV_SV
`define MERGE_ITEMS_ENV_SV

package merge_items;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "sequencer.sv"
    `include "model.sv"
    `include "scoreboard.sv"
    `include "env.sv"

endpackage

`endif
