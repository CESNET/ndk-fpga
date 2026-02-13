//-- sequencer.sv: Sequencer for axis interface
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class sequencer #(
    int unsigned ITEMS,
    int unsigned ITEM_WIDTH,
    int unsigned TUSER_WIDTH
) extends uvm_sequencer #(uvm_axi::sequence_item #(ITEMS, ITEM_WIDTH, TUSER_WIDTH));
    // ------------------------------------------------------------------------
    // Registration of agent to databaze
    `ndk_component_param_utils(
        uvm_axi::sequencer#(ITEMS, ITEM_WIDTH, TUSER_WIDTH),
        $sformatf("uvm_axi::sequencer#(%0d,%0d,%0d)",ITEMS, ITEM_WIDTH, TUSER_WIDTH)
    )

    uvm_reset::sync_terminate reset_sync;

    // Constructor
    function new(string name = "sequencer", uvm_component parent = null);
        super.new(name, parent);
        reset_sync = new();
    endfunction: new

endclass

