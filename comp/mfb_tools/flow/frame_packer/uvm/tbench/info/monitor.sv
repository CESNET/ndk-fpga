// monitor.sv
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): David Beneš <xbenes52@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class monitor #(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH) extends uvm_monitor;
    `uvm_component_param_utils(uvm_meta::monitor #(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH))

    // Used to send transactions to all connected components.
    uvm_analysis_port #(sequence_item #(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH)) analysis_port;
    sequence_item #(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH) item;

    // Creates new instance of this class.
    function new (string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Instantiates child components.
    function void build_phase(uvm_phase phase);
        analysis_port = new("analysis port", this);
        item = sequence_item #(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH)::type_id::create("item");
    endfunction

endclass

