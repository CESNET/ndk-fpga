/*
 * file       : pkg.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: byte array pkg
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef LOGIC_VECTOR_ARRAY_PKG
`define LOGIC_VECTOR_ARRAY_PKG

package uvm_logic_vector_array;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "config.sv"
    `include "sequence_item.sv"
    `include "sequencer.sv"
    `include "sequence.sv"
    `include "monitor.sv"
    `include "agent.sv"

    `include "meter.sv"

endpackage

`endif
