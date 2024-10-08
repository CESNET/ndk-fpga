// sequencer.sv: Sequencer for the LBUS interface
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class sequencer extends uvm_sequencer #(sequence_item);
    `uvm_component_utils(uvm_lbus::sequencer)

    // Constructor
    function new(string name = "sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction

endclass
