//-- sequencer.sv: Sequencer for AVST interface
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class sequencer #(int unsigned REGIONS, int unsigned REGION_SIZE, int unsigned BLOCK_SIZE, int unsigned ITEM_WIDTH, int unsigned META_WIDTH) extends uvm_sequencer #(uvm_avst::sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH));
    // ------------------------------------------------------------------------
    // Registration of agent to databaze
    `uvm_component_param_utils(uvm_avst::sequencer #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))

    uvm_reset::sync_terminate reset_sync;

    // Constructor
    function new(string name = "sequencer", uvm_component parent = null);
        super.new(name, parent);
        reset_sync = new();
    endfunction: new

endclass

