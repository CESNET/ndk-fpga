//-- sequencer.sv: Sequencer for logic vector
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class sequencer #(int unsigned DATA_WIDTH) extends uvm_sequencer #(sequence_item #(DATA_WIDTH));
    `uvm_component_param_utils(uvm_logic_vector::sequencer #(DATA_WIDTH))

    function new(string name = "sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction

endclass

