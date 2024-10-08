//-- pkg.sv: Package for environment
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef SPEED_METER_ENV_SV
`define SPEED_METER_ENV_SV

package uvm_speed_meter;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "sequence_tb.sv"
    `include "sequencer.sv"
    `include "env.sv"

endpackage

`endif
