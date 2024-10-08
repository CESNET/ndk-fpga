// sequencer.sv: Sequencer for AVST credit control interface
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class sequencer #(int unsigned UPDATE_CNT_WIDTH) extends uvm_sequencer #(uvm_avst_crdt::sequence_item #(UPDATE_CNT_WIDTH));
    `uvm_component_param_utils(uvm_avst_crdt::sequencer #(UPDATE_CNT_WIDTH))

    // Constructor
    function new(string name = "sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction

endclass
