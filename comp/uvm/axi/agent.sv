//-- agent.sv: AXI agent
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// This is AXI rx agent, which declares basic components.
class agent_rx #(int unsigned DATA_WIDTH, int unsigned TUSER_WIDTH, int unsigned REGIONS) extends uvm_agent;

    // ------------------------------------------------------------------------
    // Registration of agent to databaze
    `uvm_component_param_utils(uvm_axi::agent_rx #(DATA_WIDTH, TUSER_WIDTH, REGIONS))

    // ------------------------------------------------------------------------
    // Variables
    uvm_analysis_port #(sequence_item #(DATA_WIDTH, TUSER_WIDTH, REGIONS)) analysis_port;

    // ------------------------------------------------------------------------
    // Agent's base components
    sequencer       #(DATA_WIDTH, TUSER_WIDTH, REGIONS) m_sequencer;
    driver_rx       #(DATA_WIDTH, TUSER_WIDTH, REGIONS) m_driver;
    monitor         #(DATA_WIDTH, TUSER_WIDTH, REGIONS) m_monitor;
    config_item                                         m_config;

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
            m_sequencer = sequencer #(DATA_WIDTH, TUSER_WIDTH, REGIONS)::type_id::create("m_sequencer", this);
            m_driver    = driver_rx #(DATA_WIDTH, TUSER_WIDTH, REGIONS)::type_id::create("m_driver", this);
        end

        // Create monitor
        m_monitor   = monitor #(DATA_WIDTH, TUSER_WIDTH, REGIONS)::type_id::create("m_monitor", this);
    endfunction

    virtual function uvm_active_passive_enum get_is_active();
        return uvm_active_passive_enum'(m_config.active);
    endfunction

    function void connect_phase(uvm_phase phase);

        // Interface to connect with
        virtual axi_if #(DATA_WIDTH, TUSER_WIDTH) vif;

        super.connect_phase(phase);

        // Get interface instance
        if(!uvm_config_db #(virtual axi_if #(DATA_WIDTH, TUSER_WIDTH))::get(null, "", m_config.interface_name, vif)) begin
            `uvm_fatal(this.get_full_name(), {"\n\tCannot find 'axi_if' with name ", m_config.interface_name, " inside uvm_config_db, probably not set!"})
        end

        // Connect driver if the agent is active
        if(get_is_active() == UVM_ACTIVE) begin
            m_driver.vif = vif;
            m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
        end

        // Connect monitor
        m_monitor.vif = vif;
        analysis_port = m_monitor.analysis_port;
    endfunction

endclass

// This is AXI tx agent, which declares basic components.
class agent_tx #(int unsigned DATA_WIDTH, int unsigned TUSER_WIDTH, int unsigned REGIONS) extends uvm_agent;

    // ------------------------------------------------------------------------
    // Registration of agent to databaze
    `uvm_component_param_utils(uvm_axi::agent_tx #(DATA_WIDTH, TUSER_WIDTH, REGIONS))

    // ------------------------------------------------------------------------
    // Variables
    uvm_analysis_port #(sequence_item #(DATA_WIDTH, TUSER_WIDTH, REGIONS)) analysis_port;

    // ------------------------------------------------------------------------
    // Agent's base components
    sequencer       #(DATA_WIDTH, TUSER_WIDTH, REGIONS) m_sequencer;
    driver_tx       #(DATA_WIDTH, TUSER_WIDTH, REGIONS) m_driver;
    monitor         #(DATA_WIDTH, TUSER_WIDTH, REGIONS) m_monitor;
    config_item                                                                 m_config;

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
            m_sequencer = sequencer #(DATA_WIDTH, TUSER_WIDTH, REGIONS)::type_id::create("m_sequencer", this);
            m_driver    = driver_tx #(DATA_WIDTH, TUSER_WIDTH, REGIONS)::type_id::create("m_driver", this);
        end

        // Create monitor
        m_monitor   = monitor #(DATA_WIDTH, TUSER_WIDTH, REGIONS)::type_id::create("m_monitor", this);
    endfunction

    virtual function uvm_active_passive_enum get_is_active();
        return uvm_active_passive_enum'(m_config.active);
    endfunction

    function void connect_phase(uvm_phase phase);

        // Interface to connect with
        virtual axi_if #(DATA_WIDTH, TUSER_WIDTH) vif;

        super.connect_phase(phase);

        // Get interface instance
        if(!uvm_config_db #(virtual axi_if #(DATA_WIDTH, TUSER_WIDTH))::get(null, "", m_config.interface_name, vif)) begin
            `uvm_fatal(this.get_full_name(), {"\n\tCannot find 'axi_if' with name ", m_config.interface_name, " inside uvm_config_db, probably not set!"})
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
