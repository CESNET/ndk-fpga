// sequencer.sv
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class sequencer#(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH) extends uvm_sequencer #(sequence_item#(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH));
    `uvm_component_utils(uvm_header_type::sequencer#(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH))

    uvm_reset::sync_terminate reset_sync;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        reset_sync = new();
    endfunction
endclass
