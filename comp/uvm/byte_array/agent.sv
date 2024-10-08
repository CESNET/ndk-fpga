/*
 * file       : agent.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: Byte array agent
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef BYTE_ARRAY_AGENT_SV
`define BYTE_ARRAY_AGENT_SV

class agent extends uvm_agent;

    // registration of component tools
    `uvm_component_utils(uvm_byte_array::agent)

    // -----------------------
    // Variables.
    // -----------------------

    uvm_analysis_port #(sequence_item) analysis_port;
    monitor m_monitor;
    sequencer m_sequencer;
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

        m_monitor = monitor::type_id::create("m_monitor", this);
        if(get_is_active() == UVM_ACTIVE) begin
            m_sequencer = sequencer::type_id::create("m_sequencer", this);
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
