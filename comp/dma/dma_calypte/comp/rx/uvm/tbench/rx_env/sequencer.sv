//-- sequencer.sv
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class sequencer extends uvm_sequencer;
    `uvm_component_utils(uvm_dma_ll_rx::sequencer);

    uvm_byte_array::sequencer  m_data;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

endclass


