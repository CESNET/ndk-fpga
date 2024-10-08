// pkg.sv: Package for sequence library
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

`ifndef UVM_PACKET_GENERATORS_PKG
`define UVM_PACKET_GENERATORS_PKG

package uvm_packet_generators;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "config.sv"

    // FlowTest sequence parameters
    parameter GENERATOR_EXECUTE_PATH = "ft-generator";
    parameter CONFIG_GENERATOR_EXECUTE_PATH = { "`dirname ", `__FILE__, "`/flowtest/tools/config_generator.py" };
    parameter PROFILE_GENERATOR_EXECUTE_PATH = { "`dirname ", `__FILE__, "`/flowtest/tools/profile_generator.py" };
    `include "sequence_flowtest.sv"

    // Search sequence parameters
    parameter PKT_GEN_PATH = {"`dirname ", `__FILE__, "`/search/pkt_gen.py"};
    `include "sequence_search.sv"

    `include "sequence_library.sv"

endpackage

`endif
