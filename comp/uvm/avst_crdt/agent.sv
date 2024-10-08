// agent.sv: AVST credit control agent
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

// ======= //
// RX side //
// ======= //

class agent_rx #(int unsigned UPDATE_CNT_WIDTH) extends uvm_agent;
    `uvm_component_param_utils(uvm_avst_crdt::agent_rx #(UPDATE_CNT_WIDTH))

    // Analysis port
    uvm_analysis_port #(sequence_item #(UPDATE_CNT_WIDTH)) analysis_port;

    // ------------------ //
    // Agent's components //
    // ------------------ //

    sequencer #(UPDATE_CNT_WIDTH) m_sequencer;
    driver_rx #(UPDATE_CNT_WIDTH) m_driver;
    monitor   #(UPDATE_CNT_WIDTH) m_monitor;
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
            m_sequencer = sequencer #(UPDATE_CNT_WIDTH)::type_id::create("m_sequencer", this);
            m_driver    = driver_rx #(UPDATE_CNT_WIDTH)::type_id::create("m_driver",    this);
        end

        // Create a monitor
        m_monitor = monitor #(UPDATE_CNT_WIDTH)::type_id::create("m_monitor", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        // Virtual interface
        virtual avst_crdt_if #(UPDATE_CNT_WIDTH) vif;

        super.connect_phase(phase);

        // Get a virtual interface instance from the database
        assert(uvm_config_db #(virtual avst_crdt_if #(UPDATE_CNT_WIDTH))::get(null, "", m_config.interface_name, vif))
        else begin
            `uvm_fatal(this.get_full_name(), $sformatf("Cannot find an interface with name %s, probably not set!", m_config.interface_name));
        end

        // Connect the driver if the agent is active
        if(get_is_active() == UVM_ACTIVE) begin
            m_driver.vif = vif;
            m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
        end

        // Connect the monitor
        m_monitor.vif = vif;
        analysis_port = m_monitor.analysis_port;
    endfunction

endclass

class agent_rx_hdr extends agent_rx #(2);
    `uvm_component_utils(uvm_avst_crdt::agent_rx_hdr)

    // Constructor
    function new(string name = "agent_rx_hdr", uvm_component parent = null);
        super.new(name, parent);
    endfunction

endclass

class agent_rx_data extends agent_rx #(4);
    `uvm_component_utils(uvm_avst_crdt::agent_rx_data)

    // Constructor
    function new(string name = "agent_rx_data", uvm_component parent = null);
        super.new(name, parent);
    endfunction

endclass

// ======= //
// TX side //
// ======= //

class agent_tx #(int unsigned UPDATE_CNT_WIDTH) extends uvm_agent;
    `uvm_component_param_utils(uvm_avst_crdt::agent_tx #(UPDATE_CNT_WIDTH))

    // Analysis port
    uvm_analysis_port #(sequence_item #(UPDATE_CNT_WIDTH)) analysis_port;

    // ------------------ //
    // Agent's components //
    // ------------------ //

    sequencer #(UPDATE_CNT_WIDTH) m_sequencer;
    driver_tx #(UPDATE_CNT_WIDTH) m_driver;
    monitor   #(UPDATE_CNT_WIDTH) m_monitor;
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

        // Get a configuration from the database
        assert(uvm_config_db #(config_item)::get(this, "", "m_config", m_config))
        else begin
            `uvm_fatal(this.get_full_name(), "Unable to get configuration object")
        end

        // Create a sequencer and a driver if the agent is active
        if(get_is_active() == UVM_ACTIVE) begin
            m_sequencer = sequencer #(UPDATE_CNT_WIDTH)::type_id::create("m_sequencer", this);
            m_driver    = driver_tx #(UPDATE_CNT_WIDTH)::type_id::create("m_driver",    this);
        end

        // Create a monitor
        m_monitor = monitor #(UPDATE_CNT_WIDTH)::type_id::create("m_monitor", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        // Virtual interface
        virtual avst_crdt_if #(UPDATE_CNT_WIDTH) vif;

        super.connect_phase(phase);

        // Get a virtual interface instance from the database
        assert(uvm_config_db #(virtual avst_crdt_if #(UPDATE_CNT_WIDTH))::get(null, "", m_config.interface_name, vif))
        else begin
            `uvm_fatal(this.get_full_name(), $sformatf("Cannot find an interface with name %s, probably not set!", m_config.interface_name));
        end

        // Connect the driver if the agent is active
        if(get_is_active() == UVM_ACTIVE) begin
            m_driver.vif = vif;
            m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
        end

        // Connect the monitor
        m_monitor.vif = vif;
        analysis_port = m_monitor.analysis_port;
    endfunction

endclass

class agent_tx_hdr extends agent_tx #(2);
    `uvm_component_utils(uvm_avst_crdt::agent_tx_hdr)

    // Constructor
    function new(string name = "agent_tx_hdr", uvm_component parent = null);
        super.new(name, parent);
    endfunction

endclass

class agent_tx_data extends agent_tx #(4);
    `uvm_component_utils(uvm_avst_crdt::agent_tx_data)

    // Constructor
    function new(string name = "agent_tx_data", uvm_component parent = null);
        super.new(name, parent);
    endfunction

endclass
