//-- pkg.sv: Package for environment
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author:   Oliver Gurka <xgurka00@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef GEN_MVB_MUX_ENV_SV
`define GEN_MVB_MUX_ENV_SV

package uvm_mvb_mux;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "comparer.sv"
    `include "sequencer.sv"
    `include "model.sv"
    `include "scoreboard.sv"
    `include "env.sv"

endpackage

`endif
