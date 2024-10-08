/*
 * file       : agent.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: RESET agent
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


class agent extends uvm_agent;
    `uvm_component_utils(uvm_reset::agent);

    uvm_analysis_port #(sequence_item) analysis_port;

    // -----------------------
    // Variables.
    // -----------------------
    sequencer m_sequencer;
    driver    m_driver;
    monitor   m_monitor;
    // configuration object set if agent is passive or active and iterface name
    config_item m_config;

    // constructors
    function new (string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        if (!uvm_config_db#(config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(this.get_type_name(), "Unable to get configuration object");
        end

        if (this.get_is_active() == UVM_ACTIVE) begin
            m_sequencer = sequencer::type_id::create("m_sequencer", this);
            m_driver    = driver::type_id::create("m_driver", this);
        end

        m_monitor = monitor::type_id::create("m_monitor", this);
    endfunction

    virtual function uvm_active_passive_enum get_is_active();
        return uvm_active_passive_enum'(m_config.active);
    endfunction

    function void sync_connect(sync s);
        m_monitor.sync_connect(s);
    endfunction

    function void connect_phase(uvm_phase phase);
        virtual reset_if vif;

        super.connect_phase(phase);
        if (!uvm_config_db#(virtual reset_if)::get(this, "", m_config.interface_name, vif)) begin
            `uvm_fatal(this.get_type_name(), {"cannot find interface ", m_config.interface_name});
        end

        m_monitor.vif = vif;
        analysis_port = m_monitor.analysis_port;

        if (this.get_is_active() == UVM_ACTIVE) begin
            m_driver.vif = vif;
            m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
        end
    endfunction
endclass
