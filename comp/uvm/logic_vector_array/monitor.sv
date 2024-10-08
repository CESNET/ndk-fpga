/*
 * file       : monitor.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: byte array monitor
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef LOGIC_VECTOR_ARRAY_MONITOR_SV
`define LOGIC_VECTOR_ARRAY_MONITOR_SV

class monitor #(int unsigned ITEM_WIDTH) extends uvm_monitor;

    `uvm_component_utils(uvm_logic_vector_array::monitor #(ITEM_WIDTH))

    // Used to send transactions to all connected components.
    uvm_analysis_port #(sequence_item #(ITEM_WIDTH)) analysis_port;

    // Creates new instance of this class.
    function new (string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Instantiates child components.
    function void build_phase(uvm_phase phase);
        analysis_port = new("analysis port", this);
    endfunction

endclass

`endif
