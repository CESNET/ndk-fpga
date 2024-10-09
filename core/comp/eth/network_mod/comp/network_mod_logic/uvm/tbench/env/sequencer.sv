// sequencer.sv: Virtual sequencer 
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kondys <xkondy00@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause 

class virt_sequencer#(ITEM_WIDTH, META_WIDTH) extends uvm_sequencer;
    `uvm_component_param_utils(virt_sequencer#(ITEM_WIDTH, META_WIDTH))

    logic_vector_array::sequencer#(ITEM_WIDTH) m_byte_array_sqr;
    logic_vector::sequencer#(META_WIDTH) m_logic_vector_sqr;

    function new(string name = "virt_sequencer", uvm_component parent);
        super.new(name, parent);
    endfunction

endclass
