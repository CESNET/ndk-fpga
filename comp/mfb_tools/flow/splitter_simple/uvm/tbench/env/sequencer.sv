//-- sequencer.sv: Virtual sequencer
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class virt_sequencer#(META_WIDTH) extends uvm_sequencer;

    `uvm_component_param_utils(virt_sequencer#(META_WIDTH))

    uvm_logic_vector_array::sequencer m_byte_array_sqr;
    uvm_logic_vector::sequencer#(META_WIDTH) m_logic_vector_sqr;

    function new(string name = "virt_sequencer", uvm_component parent);
        super.new(name, parent);
    endfunction

endclass
