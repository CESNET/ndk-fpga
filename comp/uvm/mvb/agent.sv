//-- agent.sv: Mvb agent
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef MVB_AGENT_SV
`define MVB_AGENT_SV

// This is mvb rx agent, which declares basic components.
class agent_rx #(int unsigned ITEMS, int unsigned ITEM_WIDTH) extends uvm_agent;
    `uvm_component_param_utils(uvm_mvb::agent_rx #(ITEMS, ITEM_WIDTH))

    // ------------------------------------------------------------------------
    // Variables
    uvm_analysis_port #(sequence_item #(ITEMS, ITEM_WIDTH)) analysis_port;

    // ------------------------------------------------------------------------
    // Agent's base components
    uvm_reset::sync_cbs                  reset_sync;
    sequencer       #(ITEMS, ITEM_WIDTH) m_sequencer;
    driver_rx       #(ITEMS, ITEM_WIDTH) m_driver;
    monitor         #(ITEMS, ITEM_WIDTH) m_monitor;
    config_item                          m_config;

    // ------------------------------------------------------------------------
    // Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
        reset_sync = new();
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
            m_sequencer = sequencer #(ITEMS, ITEM_WIDTH)::type_id::create("m_sequencer", this);
            m_driver    = driver_rx #(ITEMS, ITEM_WIDTH)::type_id::create("m_driver", this);
        end

        // Create monitor
        m_monitor   = monitor #(ITEMS, ITEM_WIDTH)::type_id::create("m_monitor", this);
    endfunction

    virtual function uvm_active_passive_enum get_is_active();
        return uvm_active_passive_enum'(m_config.active);
    endfunction

    function void connect_phase(uvm_phase phase);

        // Interface to connect with
        virtual mvb_if #(ITEMS, ITEM_WIDTH) vif;

        super.connect_phase(phase);

        // Get interface instance
        if(!uvm_config_db #(virtual mvb_if #(ITEMS, ITEM_WIDTH))::get(null, "", m_config.interface_name, vif)) begin
            `uvm_fatal(this.get_full_name(), {"Cannot find 'mvb_if' with name ",  m_config.interface_name," inside uvm_config_db, probably not set!"})
        end

        // Connect driver if the agent is active
        if(get_is_active() == UVM_ACTIVE) begin
            m_driver.vif = vif;
            m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
            // Connect reset
            reset_sync.push_back(m_sequencer.reset_sync);
        end

        // Connect monitor
        m_monitor.vif = vif;
        analysis_port = m_monitor.analysis_port;

    endfunction

endclass

// This is mvb tx agent, which declares basic components.
class agent_tx #(int unsigned ITEMS, int unsigned ITEM_WIDTH) extends uvm_agent;
    `uvm_component_param_utils(uvm_mvb::agent_tx #(ITEMS, ITEM_WIDTH))

    // ------------------------------------------------------------------------
    // Variables
    uvm_analysis_port #(sequence_item #(ITEMS, ITEM_WIDTH)) analysis_port;

    // ------------------------------------------------------------------------
    // Agent's base components
    uvm_reset::sync_cbs                      reset_sync;
    sequencer       #(ITEMS, ITEM_WIDTH) m_sequencer;
    driver_tx       #(ITEMS, ITEM_WIDTH) m_driver;
    monitor         #(ITEMS, ITEM_WIDTH) m_monitor;
    config_item                          m_config;

    // ------------------------------------------------------------------------
    // Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
        reset_sync = new();
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
            m_sequencer = sequencer #(ITEMS, ITEM_WIDTH)::type_id::create("m_sequencer", this);
            m_driver    = driver_tx #(ITEMS, ITEM_WIDTH)::type_id::create("m_driver", this);
        end

        // Create monitor
        m_monitor   = monitor #(ITEMS, ITEM_WIDTH)::type_id::create("m_monitor", this);
    endfunction

    virtual function uvm_active_passive_enum get_is_active();
        return uvm_active_passive_enum'(m_config.active);
    endfunction

    function void connect_phase(uvm_phase phase);

        // Interface to connect with
        virtual mvb_if #(ITEMS, ITEM_WIDTH) vif;

        super.connect_phase(phase);

        // Get interface instance
        if(!uvm_config_db #(virtual mvb_if #(ITEMS, ITEM_WIDTH))::get(null, "", m_config.interface_name, vif)) begin
            `uvm_fatal(this.get_full_name(), "Cannot find 'mvb_if' inside uvm_config_db, probably not set!")
        end

        // Connect driver if the agent is active
        m_monitor.vif = vif;
        analysis_port = m_monitor.analysis_port;

        // Connect monitor
        if(get_is_active() == UVM_ACTIVE) begin
            m_driver.vif = vif;
            m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
            // Connect reset
            reset_sync.push_back(m_sequencer.reset_sync);
        end
    endfunction

endclass

`endif
