//-- pkg.sv: Package for environment
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef MTC_ENV_SV
`define MTC_ENV_SV

package uvm_mtc;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "model.sv"
    `include "model_base.sv"
    `include "mi_subscriber.sv"
    `include "scoreboard_cmp.sv"
    `include "scoreboard.sv"
    `include "tr_planner.sv"
    `include "sequencer.sv"
    `include "sequence.sv"
    `include "monitor.sv"
    `include "env.sv"


endpackage

`endif
