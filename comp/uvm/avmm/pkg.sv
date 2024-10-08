// pkg.sv: Package for AVMM interface
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

`ifndef AVMM_PKG
`define AVMM_PKG

package uvm_avmm;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    typedef enum {
        READ,
        WRITE
    } request_item_type_e;

    `include "config.sv"
    `include "sequence_item.sv"
    `include "internal_items.sv"
    `include "request_subscriber.sv"
    `include "memory_model.sv"
    `include "sequencer.sv"
    `include "sequence.sv"
    `include "driver.sv"
    `include "monitor.sv"
    `include "coverage.sv"
    `include "statistics.sv"
    `include "agent.sv"

endpackage

`endif
