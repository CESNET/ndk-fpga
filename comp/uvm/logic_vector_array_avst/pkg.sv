//-- pkg.sv: Package for environment that includes high level byte array and low level mfb agent
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef LOGIC_VECTOR_ARRAY_AVST_PKG
`define LOGIC_VECTOR_ARRAY_AVST_PKG

package uvm_logic_vector_array_avst;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "config.sv"
    `include "data_reg.sv"
    `include "monitor.sv"
    `include "sequencer.sv"
    `include "sequence.sv"
    `include "env.sv"

endpackage

`endif
