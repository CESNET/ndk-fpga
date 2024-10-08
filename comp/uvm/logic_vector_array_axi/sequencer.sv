//-- sequencer.sv: AXI sequencer
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class sequencer_rx #(int unsigned ITEM_WIDTH) extends uvm_sequencer;
    `uvm_component_param_utils(uvm_logic_vector_array_axi::sequencer_rx #(ITEM_WIDTH));

    uvm_logic_vector_array::sequencer #(ITEM_WIDTH) m_data;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

endclass


