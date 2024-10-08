// monitor.sv
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class monitor #(MVB_ITEM_WIDTH, HEADER_SIZE) extends uvm_monitor;
    `uvm_component_param_utils(uvm_superpacket_header::monitor #(MVB_ITEM_WIDTH, HEADER_SIZE))

    // Used to send transactions to all connected components.
    uvm_analysis_port #(sequence_item #(MVB_ITEM_WIDTH, HEADER_SIZE)) analysis_port;
    sequence_item #(MVB_ITEM_WIDTH, HEADER_SIZE) item;

    // Creates new instance of this class.
    function new (string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Instantiates child components.
    function void build_phase(uvm_phase phase);
        analysis_port = new("analysis port", this);
        item = sequence_item #(MVB_ITEM_WIDTH, HEADER_SIZE)::type_id::create("item");
    endfunction

endclass

