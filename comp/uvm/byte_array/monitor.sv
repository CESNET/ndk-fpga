/*
 * file       : monitor.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: byte array monitor
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef BYTE_ARRAY_MONITOR_SV
`define BYTE_ARRAY_MONITOR_SV

class monitor extends uvm_monitor;

    `uvm_component_utils(uvm_byte_array::monitor)

    // Used to send transactions to all connected components.
    uvm_analysis_port #(sequence_item) analysis_port;
    sequence_item item;

    // Creates new instance of this class.
    function new (string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Instantiates child components.
    function void build_phase(uvm_phase phase);
        analysis_port = new("analysis port", this);
        item = sequence_item::type_id::create("item");
    endfunction

endclass

`endif
