//-- pkg.sv: Package for environment that includes high level byte array and low level mfb agent
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef BYTE_ARRAY_MFB_PKG
`define BYTE_ARRAY_MFB_PKG

package uvm_byte_array_mfb;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "config.sv"
    `include "monitor.sv"
    `include "sequencer.sv"
    `include "sequence.sv"
    `include "env.sv"

endpackage

`endif
