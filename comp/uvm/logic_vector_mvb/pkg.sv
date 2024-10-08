//-- pkg.sv: Package for environment that includes high level byte array and low level mvb agent
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef LOGIC_VECTOR_MVB_PKG
`define LOGIC_VECTOR_MVB_PKG

package uvm_logic_vector_mvb;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "config.sv"
    `include "monitor.sv"
    `include "sequence.sv"
    `include "env.sv"

endpackage

`endif
