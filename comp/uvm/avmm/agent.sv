// agent.sv: AVMM agent
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

// Slave
class agent_slave #(int unsigned ADDRESS_WIDTH, int unsigned DATA_WIDTH, int unsigned BURST_WIDTH) extends uvm_agent;
    `uvm_component_param_utils(uvm_avmm::agent_slave #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH))

    // --------- //
    // Variables //
    // --------- //

    // Analysis ports
    uvm_analysis_port #(sequence_item_request  #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH)) analysis_port_request;
    uvm_analysis_port #(sequence_item_response #(DATA_WIDTH))                             analysis_port_response;

    // Agent's base components
    sequencer_slave #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH) m_sequencer;
    driver_slave    #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH) m_driver;
    monitor         #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH) m_monitor;
    coverage        #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH) m_coverage;
    statistics      #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH) m_statistics;
    config_item                                               m_config;

    // Constructor
    function new(string name = "agent_slave", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // --------- //
    // Functions //
    // --------- //

    virtual function uvm_active_passive_enum get_is_active();
        return uvm_active_passive_enum'(m_config.active);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        // Get configuration object
        assert(uvm_config_db #(config_item)::get(this, "", "m_config", m_config))
        else begin
            `uvm_fatal(this.get_full_name(), "Unable to get configuration object")
        end

        // Create sequencer and driver if the agent is active
        if(get_is_active() == UVM_ACTIVE) begin
            m_sequencer = sequencer_slave #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH)::type_id::create("m_sequencer", this);
            m_driver    = driver_slave    #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH)::type_id::create("m_driver",    this);
        end

        // Create monitor
        m_monitor = monitor #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH)::type_id::create("m_monitor", this);
        // Create coverage
        m_coverage = coverage #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH)::type_id::create("m_coverage", this);
        // Create statistics gatherer
        m_statistics = statistics #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH)::type_id::create("m_statistics", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        // Interface to connect with
        virtual avmm_if #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH) vif;

        super.connect_phase(phase);

        // Get interface instance
        assert(uvm_config_db #(virtual avmm_if #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH))::get(null, "", m_config.interface_name, vif))
        else begin
            `uvm_fatal(this.get_full_name(), $sformatf("Cannot find '%s' interface inside uvm_config_db, probably not set!", m_config.interface_name))
        end

        // Connect driver if the agent is active
        if(get_is_active() == UVM_ACTIVE) begin
            m_driver.vif = vif;
            m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
        end

        // Connect monitor
        m_monitor.vif = vif;
        analysis_port_request  = m_monitor.analysis_port_request;
        analysis_port_response = m_monitor.analysis_port_response;

        // Connect coverage
        analysis_port_response.connect(m_coverage.analysis_export_slave);
        analysis_port_request .connect(m_coverage.analysis_export_master);
        // Connect statistics gatherer
        analysis_port_response.connect(m_statistics.analysis_export_slave);
        analysis_port_request .connect(m_statistics.analysis_export_master);
    endfunction

endclass

// Master
class agent_master #(int unsigned ADDRESS_WIDTH, int unsigned DATA_WIDTH, int unsigned BURST_WIDTH) extends uvm_agent;
    `uvm_component_param_utils(uvm_avmm::agent_master #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH))

    // --------- //
    // Variables //
    // --------- //

    // Analysis ports
    uvm_analysis_port #(sequence_item_request  #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH)) analysis_port_request;
    uvm_analysis_port #(sequence_item_response #(DATA_WIDTH))                             analysis_port_response;

    // Agent's base components
    sequencer_master #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH) m_sequencer;
    driver_master    #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH) m_driver;
    monitor          #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH) m_monitor;
    coverage         #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH) m_coverage;
    statistics       #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH) m_statistics;
    config_item                                                m_config;

    // Agent's memory model components
    memory_model       #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH) m_memory_model;
    request_subscriber #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH) m_request_subscriber;

    // Reset
    uvm_reset::sync_cbs reset_sync;

    // Constructor
    function new(string name = "agent_master", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // --------- //
    // Functions //
    // --------- //

    virtual function uvm_active_passive_enum get_is_active();
        return uvm_active_passive_enum'(m_config.active);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        reset_sync = new();

        // Get configuration object
        if(!uvm_config_db #(config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(this.get_full_name(), "Unable to get configuration object")
        end

        // Create sequencer, driver and memory model if the agent is active
        if(get_is_active() == UVM_ACTIVE) begin
            // Set configuration object for the memory model
            uvm_config_db #(config_item)::set(this, "m_memory_model", "m_config", m_config);

            m_sequencer          = sequencer_master   #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH)::type_id::create("m_sequencer",          this);
            m_driver             = driver_master      #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH)::type_id::create("m_driver",             this);
            m_memory_model       = memory_model       #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH)::type_id::create("m_memory_model",       this);
            m_request_subscriber = request_subscriber #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH)::type_id::create("m_request_subscriber", this);
        end

        // Creates monitor
        m_monitor = monitor #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH)::type_id::create("m_monitor", this);
        // Creates coverage
        m_coverage = coverage #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH)::type_id::create("m_coverage", this);
        // Creates statistics gatherer
        m_statistics = statistics #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH)::type_id::create("m_statistics", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        // Interface to connect with
        virtual avmm_if #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH) vif;

        super.connect_phase(phase);

        assert(uvm_config_db #(virtual avmm_if #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH))::get(null, "", m_config.interface_name, vif))
        else begin
            `uvm_fatal(this.get_full_name(), $sformatf("Cannot find '%s' interface inside uvm_config_db, probably not set!", m_config.interface_name))
        end

        // Connect monitor
        m_monitor.vif = vif;
        analysis_port_request  = m_monitor.analysis_port_request;
        analysis_port_response = m_monitor.analysis_port_response;

        // Connect coverage
        analysis_port_response.connect(m_coverage.analysis_export_slave);
        analysis_port_request .connect(m_coverage.analysis_export_master);
        // Connect statistics gatherer
        analysis_port_response.connect(m_statistics.analysis_export_slave);
        analysis_port_request.connect(m_statistics.analysis_export_master);

        // Connect driver and memory model if the agent is active
        if(get_is_active() == UVM_ACTIVE) begin
            m_driver.vif = vif;
            m_driver.seq_item_port.connect(m_sequencer.seq_item_export);

            // Connect memory model components
            analysis_port_request.connect(m_request_subscriber.analysis_export);
            m_request_subscriber.analysis_port.connect(m_memory_model.request_in.analysis_export);
            m_memory_model.response_out.connect(m_sequencer.response_in.analysis_export);

            // Connect reset
            reset_sync.push_back(m_sequencer.reset_sync);
            reset_sync.push_back(m_request_subscriber.reset_sync);
        end
    endfunction

endclass
