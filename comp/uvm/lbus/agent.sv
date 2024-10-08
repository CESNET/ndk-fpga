// agent.sv: LBUS agent
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

// ======= //
// TX side //
// ======= //

class agent_tx extends uvm_agent;
    `uvm_component_utils(uvm_lbus::agent_tx)

    // Analysis port
    uvm_analysis_port #(sequence_item) analysis_port;

    // ------------------ //
    // Agent's components //
    // ------------------ //

    sequencer   m_sequencer;
    driver_tx   m_driver;
    monitor     m_monitor;
    statistics  m_statistics;
    coverage    m_coverage;
    config_item m_config;

    // Constructor
    function new(string name = "agent_tx", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function uvm_active_passive_enum get_is_active();
        return uvm_active_passive_enum'(m_config.active);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        // Get a configuration object from the database
        assert(uvm_config_db #(config_item)::get(this, "", "m_config", m_config))
        else begin
            `uvm_fatal(this.get_full_name(), "Unable to get a configuration object")
        end

        // Create a sequencer and a driver if the agent is active
        if(get_is_active() == UVM_ACTIVE) begin
            m_sequencer = sequencer::type_id::create("m_sequencer", this);
            m_driver    = driver_tx::type_id::create("m_driver",    this);
        end

        // Create a monitor
        m_monitor = monitor::type_id::create("m_monitor", this);
        // Create a statistics gatherer
        m_statistics = statistics::type_id::create("m_statistics", this);
        // Create a coverage gatherer
        m_coverage = coverage::type_id::create("coverage", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        // Virtual interface
        virtual lbus_if vif;

        super.connect_phase(phase);

        // Get a virtual interface instance from the database
        assert(uvm_config_db #(virtual lbus_if)::get(null, "", m_config.interface_name, vif))
        else begin
            `uvm_fatal(this.get_full_name(), $sformatf("Cannot find an interface with the name %s, probably not set!", m_config.interface_name));
        end

        // Connect the driver if the agent is active
        if(get_is_active() == UVM_ACTIVE) begin
            m_driver.vif = vif;
            m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
        end

        // Connect the monitor
        m_monitor.vif = vif;
        analysis_port = m_monitor.analysis_port;
        // Connect the statistics gatherer
        analysis_port.connect(m_statistics.analysis_export);
        // Connect the coverage gatherer
        analysis_port.connect(m_coverage.analysis_export);
    endfunction

endclass

// ======= //
// RX side //
// ======= //

class agent_rx extends uvm_agent;
    `uvm_component_utils(uvm_lbus::agent_rx)

    // Analysis port
    uvm_analysis_port #(sequence_item) analysis_port;

    // ------------------ //
    // Agent's components //
    // ------------------ //

    sequencer   m_sequencer;
    driver_rx   m_driver;
    monitor     m_monitor;
    statistics  m_statistics;
    coverage    m_coverage;
    config_item m_config;

    // Constructor
    function new(string name = "agent_rx", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function uvm_active_passive_enum get_is_active();
        return uvm_active_passive_enum'(m_config.active);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        // Get a configuration from the database
        assert(uvm_config_db #(config_item)::get(this, "", "m_config", m_config))
        else begin
            `uvm_fatal(this.get_full_name(), "Unable to get configuration object")
        end

        // Create a sequencer and a driver if the agent is active
        if(get_is_active() == UVM_ACTIVE) begin
            m_sequencer = sequencer::type_id::create("m_sequencer", this);
            m_driver    = driver_rx::type_id::create("m_driver",    this);
        end

        // Create a monitor
        m_monitor = monitor::type_id::create("m_monitor", this);
        // Create a statistics gatherer
        m_statistics = statistics::type_id::create("m_statistics", this);
        // Create a coverage gatherer
        m_coverage = coverage::type_id::create("coverage", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        // Virtual interface
        virtual lbus_if vif;

        super.connect_phase(phase);

        // Get a virtual interface instance from the database
        assert(uvm_config_db #(virtual lbus_if)::get(null, "", m_config.interface_name, vif))
        else begin
            `uvm_fatal(this.get_full_name(), $sformatf("Cannot find an interface with the name %s, probably not set!", m_config.interface_name));
        end

        // Connect the driver if the agent is active
        if(get_is_active() == UVM_ACTIVE) begin
            m_driver.vif = vif;
            m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
        end

        // Connect the monitor
        m_monitor.vif = vif;
        analysis_port = m_monitor.analysis_port;
        // Connect the statistics gatherer
        analysis_port.connect(m_statistics.analysis_export);
        // Connect the coverage gatherer
        analysis_port.connect(m_coverage.analysis_export);
    endfunction

endclass
