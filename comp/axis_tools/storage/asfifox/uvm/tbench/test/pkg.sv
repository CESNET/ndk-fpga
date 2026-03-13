//-- pkg.sv: Test package
//-- Copyright (C) 2026 CESNET z. s. p. o.
//-- Author(s): Tomáš Neckař <xneckat00@stud.fit.vut.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef ASFIFOX_TEST_SV
`define ASFIFOX_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "base.sv"

endpackage
`endif
