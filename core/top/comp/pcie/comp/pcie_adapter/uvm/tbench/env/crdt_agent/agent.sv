//-- agent.sv: AVST credit control agent
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause 

// This is AVST credit control rx agent, which declares basic components.
class agent_rx extends uvm_agent;

    // ------------------------------------------------------------------------
    // Registration of agent to databaze
    `uvm_component_utils(uvm_crdt::agent_rx)

    // ------------------------------------------------------------------------
    // Variables
    uvm_analysis_port #(sequence_item) analysis_port;

    // ------------------------------------------------------------------------
    // Agent's base components
    sequencer   m_sequencer;
    driver_rx   m_driver;
    monitor     m_monitor;
    config_item m_config;

    //reset sync
    uvm_reset::sync_cbs reset_sync;

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

        reset_sync = new;

        // Create sequencer and driver if the agent is active
        if(get_is_active() == UVM_ACTIVE) begin
            m_sequencer = sequencer::type_id::create("m_sequencer", this);
            m_driver    = driver_rx::type_id::create("m_driver", this);
        end

        // Create monitor
        m_monitor   = monitor::type_id::create("m_monitor", this);
    endfunction

    virtual function uvm_active_passive_enum get_is_active();
        return uvm_active_passive_enum'(m_config.active);
    endfunction

    function void connect_phase(uvm_phase phase);

        // Interface to connect with
        virtual crdt_if vif;

        super.connect_phase(phase);

        // Get interface instance
        if(!uvm_config_db #(virtual crdt_if)::get(null, "", m_config.interface_name, vif)) begin
            `uvm_fatal(this.get_full_name(), $sformatf("Cannot find 'crdt_if' with name %s, probably not set!", m_config.interface_name));
        end

        // Connect driver if the agent is active
        if(get_is_active() == UVM_ACTIVE) begin
            reset_sync.push_back(m_sequencer.reset_sync);

            m_driver.vif = vif;
            m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
        end

        // Connect monitor
        m_monitor.vif = vif;
        analysis_port = m_monitor.analysis_port;
    endfunction

endclass

// This is AVST credit control tx agent, which declares basic components.
class agent_tx extends uvm_agent;

    // ------------------------------------------------------------------------
    // Registration of agent to databaze
    `uvm_component_utils(uvm_crdt::agent_tx)

    // ------------------------------------------------------------------------
    // Variables
    uvm_analysis_port #(sequence_item) analysis_port;

    // ------------------------------------------------------------------------
    // Agent's base components
    sequencer   m_sequencer;
    driver_tx   m_driver;
    monitor     m_monitor;
    config_item m_config;

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
            m_sequencer = sequencer::type_id::create("m_sequencer", this);
            m_driver    = driver_tx::type_id::create("m_driver", this);
        end

        // Create monitor
        m_monitor   = monitor::type_id::create("m_monitor", this);
    endfunction

    virtual function uvm_active_passive_enum get_is_active();
        return uvm_active_passive_enum'(m_config.active);
    endfunction

    function void connect_phase(uvm_phase phase);

        // Interface to connect with
        virtual crdt_if vif;

        super.connect_phase(phase);

        // Get interface instance
        if(!uvm_config_db #(virtual crdt_if)::get(null, "", m_config.interface_name, vif)) begin
            `uvm_fatal(this.get_full_name(), "Cannot find 'crdt_if' inside uvm_config_db, probably not set!")
        end

        // Connect driver if the agent is active
        m_monitor.vif = vif;
        analysis_port = m_monitor.analysis_port;

        // Connect monitor
        if(get_is_active() == UVM_ACTIVE) begin
            m_driver.vif = vif;
            m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
        end
    endfunction

endclass
