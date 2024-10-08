//-- sequencer.sv: Sequencer for axis interface
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class sequencer #(int unsigned DATA_WIDTH, int unsigned TUSER_WIDTH, int unsigned REGIONS) extends uvm_sequencer #(uvm_axi::sequence_item #(DATA_WIDTH, TUSER_WIDTH, REGIONS));
    // ------------------------------------------------------------------------
    // Registration of agent to databaze
    `uvm_component_param_utils(uvm_axi::sequencer #(DATA_WIDTH, TUSER_WIDTH, REGIONS))

    uvm_reset::sync_terminate reset_sync;

    // Constructor
    function new(string name = "sequencer", uvm_component parent = null);
        super.new(name, parent);
        reset_sync = new();
    endfunction: new

endclass

