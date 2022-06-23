/*
 * file       : agent.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: top_agent
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class agent extends uvm_agent;
    // registration of component tools
    `uvm_component_utils(top_agent::agent)

    // -----------------------
    // Variables.
    // -----------------------
    uvm_reset::sync_cbs       reset_sync;
    uvm_byte_array::sequencer m_sequencer;
    driver                m_driver;

    // Contructor, where analysis port is created.
    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction: new

    // -----------------------
    // Functions.
    // -----------------------

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        reset_sync  = new();
        m_sequencer = uvm_byte_array::sequencer::type_id::create("m_sequencer", this);
        m_driver    = driver::type_id::create("m_driver", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
        reset_sync.push_back(m_sequencer.reset_sync);
        reset_sync.push_back(m_driver.reset_sync);
    endfunction
endclass

