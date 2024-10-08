// sequencer.sv
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): David Beneš <xbenes52@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class sequencer #(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH) extends uvm_sequencer #(sequence_item #(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH));
    `uvm_component_param_utils(uvm_meta::sequencer #(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH))

    uvm_reset::sync_terminate reset_sync;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        reset_sync = new();
    endfunction
endclass
