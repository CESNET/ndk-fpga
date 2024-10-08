//-- sequencer.sv: Sequencer for AVST credit control interface
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause 

class sequencer extends uvm_sequencer #(uvm_crdt::sequence_item);
    // ------------------------------------------------------------------------
    // Registration of agent to databaze
    `uvm_component_utils(uvm_crdt::sequencer)

    uvm_reset::sync_terminate reset_sync;

    // Constructor
    function new(string name = "sequencer", uvm_component parent = null);
        super.new(name, parent);
        reset_sync = new();
    endfunction: new

endclass

