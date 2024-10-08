/*
 * file       : pkg.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: Package contain common classes
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


`ifndef COMMON_PKG
`define COMMON_PKG

package uvm_common;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `uvm_analysis_imp_decl(_export)
    `uvm_analysis_imp_decl(_model)
    `uvm_analysis_imp_decl(_dut)

    `include "rand_rdy.sv"
    `include "rand_length.sv"
    `include "sync.sv"

    `include "sequence_cfg.sv"
    `include "sequence_item.sv"
    `include "sequence.sv"
    `include "sequence_library.sv"

    `include "fifo.sv"

    `include "comparer_base.sv"
    `include "comparer_tagged.sv"
    `include "comparer_ordered.sv"
    `include "comparer_unordered.sv"
    `include "comparer.sv"

    `include "stats.sv"
    `include "prog.sv"
endpackage


`endif
