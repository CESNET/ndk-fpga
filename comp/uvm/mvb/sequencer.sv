//-- sequencer.sv: Sequencer for mvb interface
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef MVB_SEQUENCER_SV
`define MVB_SEQUENCER_SV

class sequencer #(int unsigned ITEMS, int unsigned ITEM_WIDTH) extends uvm_sequencer #(uvm_mvb::sequence_item #(ITEMS, ITEM_WIDTH));

    // ------------------------------------------------------------------------
    // Registration of agent to databaze
    `uvm_component_param_utils(uvm_mvb::sequencer #(ITEMS, ITEM_WIDTH))

    // RESET
    uvm_reset::sync_terminate reset_sync;

    // Constructor
    function new(string name = "sequencer", uvm_component parent = null);
        super.new(name, parent);
        reset_sync = new();
    endfunction: new

endclass

`endif
