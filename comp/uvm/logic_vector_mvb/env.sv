//-- env.sv: Mfb environment
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// Definition of mvb environment
class env_rx #(int unsigned ITEMS, int unsigned ITEM_WIDTH) extends uvm_env;
    `uvm_component_param_utils(uvm_logic_vector_mvb::env_rx #(ITEMS, ITEM_WIDTH));

    // ------------------------------------------------------------------------
    // Definition of agents
    //sequencer_rx #(ITEM_WIDTH) m_sequencer;
    uvm_logic_vector::sequencer#(ITEM_WIDTH) m_sequencer;
    uvm_analysis_port #(uvm_logic_vector::sequence_item#(ITEM_WIDTH)) analysis_port;
    uvm_reset::sync_cbs            reset_sync;

    uvm_logic_vector::agent#(ITEM_WIDTH)   m_logic_vector_agent;
    uvm_logic_vector::meter#(ITEM_WIDTH)   m_meter;
    uvm_mvb::agent_rx #(ITEMS, ITEM_WIDTH) m_mvb_agent;

    local config_item m_config;

    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);

        uvm_mvb::config_item mvb_agent_cfg;
        uvm_logic_vector::config_item logic_vector_agent_cfg;

        if(!uvm_config_db #(config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(get_type_name(), "Unable to get configuration object")
        end

        logic_vector_agent_cfg = new;
        mvb_agent_cfg          = new;

        logic_vector_agent_cfg.active = m_config.active;

        mvb_agent_cfg.active         = m_config.active;
        mvb_agent_cfg.interface_name = m_config.interface_name;

        uvm_config_db #(uvm_logic_vector::config_item)::set(this, "m_logic_vector_agent", "m_config", logic_vector_agent_cfg);
        uvm_config_db #(uvm_mvb::config_item)::set(this, "m_mvb_agent", "m_config", mvb_agent_cfg);

        uvm_logic_vector::monitor#(ITEM_WIDTH)::type_id::set_inst_override(monitor #(ITEMS, ITEM_WIDTH)::get_type(), {this.get_full_name(), ".m_logic_vector_agent.*"});

        m_meter              = uvm_logic_vector::meter#(ITEM_WIDTH)::type_id::create("m_logic_vector_meter", this);
        m_logic_vector_agent = uvm_logic_vector::agent#(ITEM_WIDTH)::type_id::create("m_logic_vector_agent", this);
        m_mvb_agent          = uvm_mvb::agent_rx #(ITEMS, ITEM_WIDTH)::type_id::create("m_mvb_agent", this);

        if (m_config.active == UVM_ACTIVE) begin
            m_sequencer = uvm_logic_vector::sequencer#(ITEM_WIDTH)::type_id::create("m_sequencer", this);
        end

        reset_sync = new();
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);

        monitor #(ITEMS, ITEM_WIDTH) m_logic_vector_monitor;

        $cast(m_logic_vector_monitor, m_logic_vector_agent.m_monitor);
        m_mvb_agent.analysis_port.connect(m_logic_vector_monitor.analysis_export);
        analysis_port = m_logic_vector_agent.m_monitor.analysis_port;
        analysis_port.connect(m_meter.analysis_export);
        reset_sync.push_back(m_logic_vector_monitor.reset_sync);

        if (m_config.active == UVM_ACTIVE) begin
            m_sequencer = m_logic_vector_agent.m_sequencer;
            reset_sync.push_back(m_mvb_agent.m_sequencer.reset_sync);
            uvm_config_db #(uvm_logic_vector::sequencer#(ITEM_WIDTH))::set(this, "m_mvb_agent.m_sequencer", "hi_sqr", m_sequencer);
        end
    endfunction

    virtual task run_phase(uvm_phase phase);
        if (m_config.active == UVM_ACTIVE) begin
            sequence_lib_rx#(ITEMS, ITEM_WIDTH) mvb_seq = sequence_lib_rx#(ITEMS, ITEM_WIDTH)::type_id::create("mvb_seq", this);

            mvb_seq.min_random_count = 10;
            mvb_seq.max_random_count = 200;
            mvb_seq.init_sequence(m_config.seq_cfg);

            forever begin
                int verbosity;

                verbosity = this.get_report_verbosity_level(UVM_INFO, "mvb_seq");
                m_mvb_agent.m_sequencer.set_report_verbosity_level(verbosity >= 300 ? verbosity - 300 : 0);

                if(!mvb_seq.randomize()) `uvm_fatal(this.get_full_name(), "\n\tCannot randomize logic_vector_mvb rx_seq");
                mvb_seq.start(m_mvb_agent.m_sequencer);
            end
        end
    endtask

endclass


class env_tx #(int unsigned ITEMS, int unsigned ITEM_WIDTH) extends uvm_env;
    `uvm_component_param_utils(uvm_logic_vector_mvb::env_tx #(ITEMS, ITEM_WIDTH));

    //Access component
    uvm_mvb::sequencer #(ITEMS, ITEM_WIDTH) m_sequencer;
    uvm_analysis_port #(uvm_logic_vector::sequence_item#(ITEM_WIDTH)) analysis_port;
    uvm_reset::sync_cbs                                               reset_sync;

    // ------------------------------------------------------------------------
    // Definition of agents

    uvm_logic_vector::agent#(ITEM_WIDTH) m_logic_vector_agent;
    uvm_logic_vector::meter#(ITEM_WIDTH) m_meter;

    //uvm_logic_vector::config_item logic_vector_agent_cfg;

    uvm_mvb::agent_tx #(ITEMS, ITEM_WIDTH) m_mvb_agent;
    //uvm_mvb::config_item mvb_agent_cfg;

    local config_item m_config;

    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);

        uvm_mvb::config_item mvb_agent_cfg;
        uvm_logic_vector::config_item logic_vector_agent_cfg;

        if(!uvm_config_db #(config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(get_type_name(), "Unable to get configuration object")
        end

        logic_vector_agent_cfg = new;
        mvb_agent_cfg = new;

        logic_vector_agent_cfg.active = UVM_PASSIVE;

        mvb_agent_cfg.active = m_config.active;
        mvb_agent_cfg.interface_name = m_config.interface_name;

        uvm_config_db #(uvm_logic_vector::config_item)::set(this, "m_logic_vector_agent", "m_config", logic_vector_agent_cfg);
        uvm_config_db #(uvm_mvb::config_item)::set(this, "m_mvb_agent", "m_config", mvb_agent_cfg);

        uvm_logic_vector::monitor#(ITEM_WIDTH)::type_id::set_inst_override(monitor #(ITEMS, ITEM_WIDTH)::get_type(), {this.get_full_name(), ".m_logic_vector_agent.*"});
        m_meter              = uvm_logic_vector::meter#(ITEM_WIDTH)::type_id::create("m_logic_vector_meter", this);

        m_logic_vector_agent = uvm_logic_vector::agent#(ITEM_WIDTH)::type_id::create("m_logic_vector_agent", this);
        m_mvb_agent        = uvm_mvb::agent_tx #(ITEMS, ITEM_WIDTH)::type_id::create("m_mvb_agent", this);

        reset_sync = new();
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);

        monitor #(ITEMS, ITEM_WIDTH) m_logic_vector_monitor;

        $cast(m_logic_vector_monitor, m_logic_vector_agent.m_monitor);
        m_mvb_agent.analysis_port.connect(m_logic_vector_monitor.analysis_export);
        analysis_port = m_logic_vector_agent.m_monitor.analysis_port;
        analysis_port.connect(m_meter.analysis_export);
        reset_sync.push_back(m_logic_vector_monitor.reset_sync);

        m_sequencer = m_mvb_agent.m_sequencer;
    endfunction
endclass

