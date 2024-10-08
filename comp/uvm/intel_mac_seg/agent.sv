/*
 * file       : agent.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: Intel seq mac agent
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class agent_rx #(int unsigned SEGMENTS) extends uvm_agent;
    `uvm_component_param_utils(uvm_intel_mac_seg::agent_rx#(SEGMENTS))

    // ------------------------------------------------------------------------
    // Variables
    uvm_analysis_port #(sequence_item #(SEGMENTS)) analysis_port;

    // ------------------------------------------------------------------------
    // Agent's base components
    sequencer       #(SEGMENTS) m_sequencer;
    driver_rx       #(SEGMENTS) m_driver;
    monitor         #(SEGMENTS) m_monitor;
    statistic       #(SEGMENTS) m_stats;
    config_item                 m_config;

    // ------------------------------------------------------------------------
    // Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // ------------------------------------------------------------------------
    // Functions
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        // Get configurg file from
        if(!uvm_config_db #(config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(this.get_full_name(), "Unable to get configuration object")
        end

        // Create sequencer and driver if the agent is active
        if(get_is_active() == UVM_ACTIVE) begin
            m_sequencer = sequencer #(SEGMENTS)::type_id::create("m_sequencer", this);
            m_driver    = driver_rx #(SEGMENTS)::type_id::create("m_driver", this);
        end

        // Create monitor
        m_stats     = statistic#(SEGMENTS)::type_id::create("m_stats", this);
        m_monitor   = monitor #(SEGMENTS)::type_id::create("m_monitor", this);
    endfunction

    virtual function uvm_active_passive_enum get_is_active();
        return uvm_active_passive_enum'(m_config.active);
    endfunction

    function void connect_phase(uvm_phase phase);
        // Interface to connect with
        virtual intel_mac_seg_if #(SEGMENTS) vif;

        super.connect_phase(phase);
        // Get interface instance
        if(!uvm_config_db #(virtual intel_mac_seg_if #(SEGMENTS))::get(null, "", m_config.interface_name, vif)) begin
            `uvm_fatal(this.get_full_name(), "Cannot find 'intel_mac_seg_if' inside uvm_config_db, probably not set!")
        end

        // Connect driver if the agent is active
        if(get_is_active() == UVM_ACTIVE) begin
            m_driver.vif = vif;
            m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
        end

        // Connect monitor
        m_monitor.vif = vif;
        analysis_port = m_monitor.analysis_port;
        analysis_port.connect(m_stats.analysis_export);
    endfunction
endclass


class agent_tx #(int unsigned SEGMENTS) extends uvm_agent;
    `uvm_component_param_utils(uvm_intel_mac_seg::agent_tx#(SEGMENTS))

    // ------------------------------------------------------------------------
    // Variables
    uvm_analysis_port #(sequence_item #(SEGMENTS)) analysis_port;

    // ------------------------------------------------------------------------
    // Agent's base components
    sequencer       #(SEGMENTS) m_sequencer;
    driver_tx       #(SEGMENTS) m_driver;
    monitor         #(SEGMENTS) m_monitor;
    statistic       #(SEGMENTS) m_stats;
    config_item                 m_config;

    // ------------------------------------------------------------------------
    // Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // ------------------------------------------------------------------------
    // Functions
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        // Get configurg file from
        if(!uvm_config_db #(config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(this.get_full_name(), "Unable to get configuration object")
        end

        // Create sequencer and driver if the agent is active
        if(get_is_active() == UVM_ACTIVE) begin
            m_sequencer = sequencer #(SEGMENTS)::type_id::create("m_sequencer", this);
            m_driver    = driver_tx #(SEGMENTS)::type_id::create("m_driver", this);
        end

        // Create monitor
        m_stats     = statistic#(SEGMENTS)::type_id::create("m_stats", this);
        m_monitor   = monitor #(SEGMENTS)::type_id::create("m_monitor", this);
    endfunction

    virtual function uvm_active_passive_enum get_is_active();
        return uvm_active_passive_enum'(m_config.active);
    endfunction

    function void connect_phase(uvm_phase phase);
        // Interface to connect with
        virtual intel_mac_seg_if #(SEGMENTS) vif;

        super.connect_phase(phase);
        // Get interface instance
        if(!uvm_config_db #(virtual intel_mac_seg_if #(SEGMENTS))::get(null, "", m_config.interface_name, vif)) begin
            `uvm_fatal(this.get_full_name(), "Cannot find 'intel_mac_seg_if' inside uvm_config_db, probably not set!")
        end

        // Connect driver if the agent is active
        if(get_is_active() == UVM_ACTIVE) begin
            m_driver.vif = vif;
            m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
        end

        // Connect monitor
        m_monitor.vif = vif;
        analysis_port = m_monitor.analysis_port;
        analysis_port.connect(m_stats.analysis_export);
    endfunction
endclass

