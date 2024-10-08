//-- env.sv: Mfb environment
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class sequencer_rx #(int unsigned META_WIDTH) extends uvm_sequencer;
    `uvm_component_param_utils(uvm_byte_array_mfb::sequencer_rx #(META_WIDTH));

    uvm_logic_vector::sequencer#(META_WIDTH) m_meta;
    config_item::meta_type                   meta_behav;
    uvm_byte_array::sequencer                m_data;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

endclass


