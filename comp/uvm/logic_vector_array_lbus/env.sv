// env.sv: An environment for converting LBUS transactions to high-level logic vector array/logic vector transactions
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

// ======= //
// TX side //
// ======= //

class env_tx extends uvm_env;
    `uvm_component_utils(uvm_logic_vector_array_lbus::env_tx);

    // -------------- //
    // Analysis ports //
    // -------------- //

    uvm_analysis_port #(uvm_logic_vector_array::sequence_item #(8)) analysis_port_packet;
    uvm_analysis_port #(uvm_logic_vector::sequence_item       #(1)) analysis_port_error;

    // ------------------ //
    // Agent's components //
    // ------------------ //

    // Main sequencer
    sequencer_tx m_sequencer;

    // Logic vector array agent
    uvm_logic_vector_array::agent #(8) m_logic_vector_array_agent;
    uvm_logic_vector_array::config_item m_logic_vector_array_agent_cfg;

    // Logic vector agent
    uvm_logic_vector::agent #(1) m_logic_vector_agent;
    uvm_logic_vector::config_item m_logic_vector_agent_cfg;

    // LBUS agent
    uvm_lbus::agent_tx m_lbus_agent;
    uvm_lbus::config_item m_lbus_agent_cfg;

    // Configuration object
    config_item m_config;

    // Reset
    uvm_reset::sync_cbs reset_sync;

    // Constructor
    function new(string name = "env_tx", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        // Get a configuration object from the database
        assert(uvm_config_db #(config_item)::get(this, "", "m_config", m_config))
        else begin
            `uvm_fatal(get_type_name(), "Unable to get a configuration object")
        end

        // ------------------------ //
        // Logic vector array agent //
        // ------------------------ //

        // Configuration
        m_logic_vector_array_agent_cfg = new();
        m_logic_vector_array_agent_cfg.active = m_config.active;
        uvm_config_db #(uvm_logic_vector_array::config_item)::set(this, "m_logic_vector_array_agent", "m_config", m_logic_vector_array_agent_cfg);
        // Monitor instance override
        uvm_logic_vector_array::monitor #(8)::type_id::set_inst_override(
            monitor_logic_vector_array::get_type(),
            "m_logic_vector_array_agent.m_monitor",
            this
        );
        // Build
        m_logic_vector_array_agent = uvm_logic_vector_array::agent #(8)::type_id::create("m_logic_vector_array_agent", this);

        // ------------------ //
        // Logic vector agent //
        // ------------------ //

        // Configuration
        m_logic_vector_agent_cfg = new();
        m_logic_vector_agent_cfg.active = m_config.active;
        uvm_config_db #(uvm_logic_vector::config_item)::set(this, "m_logic_vector_agent", "m_config", m_logic_vector_agent_cfg);
        // Monitor instance override
        uvm_logic_vector::monitor #(1)::type_id::set_inst_override(
            monitor_logic_vector::get_type(),
            "m_logic_vector_agent.m_monitor",
            this
        );
        // Build
        m_logic_vector_agent = uvm_logic_vector::agent #(1)::type_id::create("m_logic_vector_agent", this);

        // ---------- //
        // LBUS agent //
        // ---------- //

        // Configuration
        m_lbus_agent_cfg = new();
        m_lbus_agent_cfg.active = m_config.active;
        m_lbus_agent_cfg.interface_name = m_config.interface_name;
        uvm_config_db #(uvm_lbus::config_item)::set(this, "m_lbus_agent", "m_config", m_lbus_agent_cfg);
        // Build
        m_lbus_agent = uvm_lbus::agent_tx::type_id::create("m_lbus_agent", this);

        // Build of main sequencer
        if (m_config.active == UVM_ACTIVE) begin
            m_sequencer = sequencer_tx::type_id::create("m_sequencer", this);
        end

        // Build of reset
        reset_sync = new();
    endfunction

    function void connect_phase(uvm_phase phase);
        monitor_logic_vector_array m_logic_vector_array_monitor;
        monitor_logic_vector       m_logic_vector_monitor;

        super.connect_phase(phase);

        // LBUS agent -> Logic vector array agent connection
        assert($cast(m_logic_vector_array_monitor, m_logic_vector_array_agent.m_monitor));
        m_lbus_agent.analysis_port.connect(m_logic_vector_array_monitor.analysis_export);
        analysis_port_packet = m_logic_vector_array_agent.m_monitor.analysis_port;

        // LBUS agent -> Logic vector agent connection
        assert($cast(m_logic_vector_monitor, m_logic_vector_agent.m_monitor));
        m_lbus_agent.analysis_port.connect(m_logic_vector_monitor.analysis_export);
        analysis_port_error = m_logic_vector_agent.m_monitor.analysis_port;

        // Main sequencer connection
        if (m_config.active == UVM_ACTIVE) begin
            m_sequencer.packet = m_logic_vector_array_agent.m_sequencer;
            m_sequencer.error  = m_logic_vector_agent.m_sequencer;
            uvm_config_db #(sequencer_tx)::set(this, "m_lbus_agent.m_sequencer", "hl_sequencer", m_sequencer);

            // Reset connection
            reset_sync.push_back(m_sequencer.reset_sync);
            reset_sync.push_back(m_sequencer.packet.reset_sync);
        end

        // Reset connection
        reset_sync.push_back(m_logic_vector_array_monitor.reset_sync);
        reset_sync.push_back(m_logic_vector_monitor.reset_sync);
    endfunction

    task run_phase(uvm_phase phase);
        if (m_config.active == UVM_ACTIVE) begin
            uvm_logic_vector_array_lbus::sequence_library_tx lbus_sequence_library = uvm_logic_vector_array_lbus::sequence_library_tx::type_id::create("lbus_sequence_library", this);
            lbus_sequence_library.min_random_count = 20;
            lbus_sequence_library.max_random_count = 100;

            forever begin
                assert(lbus_sequence_library.randomize())
                else begin
                    `uvm_fatal(this.get_full_name(), "\n\tCannot randomize");
                end
                lbus_sequence_library.start(m_lbus_agent.m_sequencer);
            end
        end
    endtask

endclass

// ======= //
// RX side //
// ======= //

class env_rx extends uvm_env;
    `uvm_component_utils(uvm_logic_vector_array_lbus::env_rx);

    // -------------- //
    // Analysis ports //
    // -------------- //

    uvm_analysis_port #(uvm_logic_vector_array::sequence_item #(8)) analysis_port_packet;
    uvm_analysis_port #(uvm_logic_vector::sequence_item       #(1)) analysis_port_error;

    // ------------------ //
    // Agent's components //
    // ------------------ //

    // Main sequencer
    uvm_lbus::sequencer m_sequencer;

    // Logic vector array agent
    uvm_logic_vector_array::agent #(8) m_logic_vector_array_agent;
    uvm_logic_vector_array::config_item m_logic_vector_array_agent_cfg;

    // Logic vector agent
    uvm_logic_vector::agent #(1) m_logic_vector_agent;
    uvm_logic_vector::config_item m_logic_vector_agent_cfg;

    // LBUS agent
    uvm_lbus::agent_rx m_lbus_agent;
    uvm_lbus::config_item m_lbus_agent_cfg;

    // Configuration object
    config_item m_config;

    // Reset
    uvm_reset::sync_cbs reset_sync;

    // Constructor
    function new(string name = "env_rx", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        // Get a configuration object from the database
        assert(uvm_config_db #(config_item)::get(this, "", "m_config", m_config))
        else begin
            `uvm_fatal(get_type_name(), "Unable to get a configuration object")
        end

        // ------------------------ //
        // Logic vector array agent //
        // ----------------------- //

        // Configuration
        m_logic_vector_array_agent_cfg = new();
        m_logic_vector_array_agent_cfg.active = m_config.active;
        uvm_config_db #(uvm_logic_vector_array::config_item)::set(this, "m_logic_vector_array_agent", "m_config", m_logic_vector_array_agent_cfg);
        // Monitor instance override
        uvm_logic_vector_array::monitor #(8)::type_id::set_inst_override(
            monitor_logic_vector_array::get_type(),
            "m_logic_vector_array_agent.m_monitor",
            this
        );
        // Build
        m_logic_vector_array_agent = uvm_logic_vector_array::agent #(8)::type_id::create("m_logic_vector_array_agent", this);

        // ------------------ //
        // Logic vector agent //
        // ------------------ //

        // Configuration
        m_logic_vector_agent_cfg = new();
        m_logic_vector_agent_cfg.active = m_config.active;
        uvm_config_db #(uvm_logic_vector::config_item)::set(this, "m_logic_vector_agent", "m_config", m_logic_vector_agent_cfg);
        // Monitor instance override
        uvm_logic_vector::monitor #(1)::type_id::set_inst_override(
            monitor_logic_vector::get_type(),
            "m_logic_vector_agent.m_monitor",
            this
        );
        // Build
        m_logic_vector_agent = uvm_logic_vector::agent #(1)::type_id::create("m_logic_vector_agent", this);

        // ---------- //
        // LBUS agent //
        // ---------- //

        // Configuration
        m_lbus_agent_cfg = new();
        m_lbus_agent_cfg.active = m_config.active;
        m_lbus_agent_cfg.interface_name = m_config.interface_name;
        uvm_config_db #(uvm_lbus::config_item)::set(this, "m_lbus_agent", "m_config", m_lbus_agent_cfg);
        // Build
        m_lbus_agent = uvm_lbus::agent_rx::type_id::create("m_lbus_agent", this);

        // Build of reset
        reset_sync = new();
    endfunction

    function void connect_phase(uvm_phase phase);
        monitor_logic_vector_array m_logic_vector_array_monitor;
        monitor_logic_vector       m_logic_vector_monitor;

        super.connect_phase(phase);

        // LBUS agent -> Logic vector array agent connection
        assert($cast(m_logic_vector_array_monitor, m_logic_vector_array_agent.m_monitor));
        m_lbus_agent.analysis_port.connect(m_logic_vector_array_monitor.analysis_export);
        analysis_port_packet = m_logic_vector_array_agent.m_monitor.analysis_port;

        // LBUS agent -> Logic vector agent connection
        assert($cast(m_logic_vector_monitor, m_logic_vector_agent.m_monitor));
        m_lbus_agent.analysis_port.connect(m_logic_vector_monitor.analysis_export);
        analysis_port_error = m_logic_vector_agent.m_monitor.analysis_port;

        // Main sequencer connection
        m_sequencer = m_lbus_agent.m_sequencer;

        // Reset connection
        reset_sync.push_back(m_logic_vector_array_monitor.reset_sync);
        reset_sync.push_back(m_logic_vector_monitor.reset_sync);
    endfunction

endclass
