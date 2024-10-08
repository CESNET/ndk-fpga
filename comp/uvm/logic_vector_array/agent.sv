/*
 * file       : agent.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: Byte array agent
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef LOGIC_VECTOR_ARRAY_AGENT_SV
`define LOGIC_VECTOR_ARRAY_AGENT_SV

class agent #(int unsigned ITEM_WIDTH) extends uvm_agent;

    // registration of component tools
    `uvm_component_utils(uvm_logic_vector_array::agent #(ITEM_WIDTH))

    // -----------------------
    // Variables.
    // -----------------------

    uvm_analysis_port #(sequence_item #(ITEM_WIDTH)) analysis_port;
    monitor #(ITEM_WIDTH) m_monitor;
    sequencer #(ITEM_WIDTH) m_sequencer;
    config_item m_config;

    // Contructor, where analysis port is created.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction: new

    // -----------------------
    // Functions.
    // -----------------------

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        if (!uvm_config_db #(config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(this.get_full_name(), "Cannot get configuration object")
        end

        m_monitor = monitor #(ITEM_WIDTH)::type_id::create("m_monitor", this);
        if(get_is_active() == UVM_ACTIVE) begin
            m_sequencer = sequencer #(ITEM_WIDTH)::type_id::create("m_sequencer", this);
        end
    endfunction

    virtual function uvm_active_passive_enum get_is_active();
        return uvm_active_passive_enum'(m_config.active);
    endfunction

    function void connect_phase(uvm_phase phase);

        super.connect_phase(phase);

        analysis_port = m_monitor.analysis_port;

    endfunction

endclass

`endif
