//-- sequencer.sv
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class sequencer extends uvm_sequencer;
    `uvm_component_utils(uvm_dma_up::sequencer);

    uvm_logic_vector_array::sequencer#(32) m_data;
    uvm_ptc_info::sequencer   m_info;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

endclass


