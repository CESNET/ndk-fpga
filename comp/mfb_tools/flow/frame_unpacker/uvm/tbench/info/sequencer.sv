// sequencer.sv
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class sequencer #(MVB_ITEM_WIDTH, HEADER_SIZE) extends uvm_sequencer #(sequence_item #(MVB_ITEM_WIDTH, HEADER_SIZE));
    `uvm_component_param_utils(uvm_superpacket_header::sequencer #(MVB_ITEM_WIDTH, HEADER_SIZE))

    uvm_reset::sync_terminate reset_sync;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        reset_sync = new();
    endfunction
endclass
