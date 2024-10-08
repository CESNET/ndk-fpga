//-- pkg.sv: Package for environment
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef DROPPER_ENV_SV
`define DROPPER_ENV_SV

package uvm_dropper;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "sequence_tb.sv"
    `include "sequencer.sv"
    `include "env.sv"

endpackage

`endif
