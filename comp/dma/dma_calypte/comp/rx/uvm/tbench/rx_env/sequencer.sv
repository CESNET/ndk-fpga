//-- sequencer.sv
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class sequencer#(ITEM_WIDTH) extends uvm_sequencer;
    `uvm_component_param_utils(uvm_dma_ll_rx::sequencer#(ITEM_WIDTH));

    uvm_logic_vector_array::sequencer#(ITEM_WIDTH)  m_data_sqcr;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

endclass


