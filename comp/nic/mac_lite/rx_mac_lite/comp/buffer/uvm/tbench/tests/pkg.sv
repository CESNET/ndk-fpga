// pkg.sv: Test package
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


`ifndef RX_MAC_LITE_BUFFER_TEST_SV
`define RX_MAC_LITE_BUFFER_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "sequence.sv"
    `include "test.sv"
    `include "speed.sv"
endpackage
`endif
