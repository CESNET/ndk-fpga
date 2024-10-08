//-- sequencer.sv: packet sequencer 
//-- Copyright (C) 2024 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause 

//typedef uvm_sequencer#(sequence_item) sequencer; 

class sequencer #(int unsigned ITEM_WIDTH, int unsigned META_WIDTH) extends uvm_sequencer #(sequence_item #(ITEM_WIDTH, META_WIDTH));
    `uvm_component_param_utils(uvm_app_core_top_agent::sequencer #(ITEM_WIDTH, META_WIDTH))

    uvm_reset::sync_terminate reset_sync;

    // Constructor
    function new(string name = "sequencer", uvm_component parent = null);
        super.new(name, parent);
        reset_sync = new();
    endfunction: new

endclass




