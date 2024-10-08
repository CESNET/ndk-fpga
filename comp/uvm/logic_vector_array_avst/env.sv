//-- env.sv: Mfb environment
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// Definition of mfb environment
class env_rx #(int unsigned REGIONS, int unsigned REGION_SIZE, int unsigned BLOCK_SIZE, int unsigned ITEM_WIDTH, int unsigned META_WIDTH, int unsigned READY_LATENCY) extends uvm_env;
    `uvm_component_param_utils(uvm_logic_vector_array_avst::env_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY));

    // ------------------------------------------------------------------------
    // Definition of agents
    sequencer_rx #(ITEM_WIDTH, META_WIDTH) m_sequencer;
    uvm_analysis_port #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)) analysis_port_data;
    uvm_analysis_port #(uvm_logic_vector::sequence_item#(META_WIDTH))       analysis_port_meta;
    uvm_reset::sync_cbs reset_sync;

    uvm_logic_vector_array::agent#(ITEM_WIDTH) m_logic_vector_array_agent;
    uvm_logic_vector_array::config_item        logic_vector_array_agent_cfg;

    uvm_logic_vector::agent#(META_WIDTH) m_logic_vector_agent;
    uvm_logic_vector::config_item        logic_vector_agent_cfg;

    uvm_avst::agent_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) m_avst_agent;
    uvm_avst::config_item avst_agent_cfg;

    config_item m_config;

    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);

        if(!uvm_config_db #(config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(get_type_name(), "Unable to get configuration object")
        end

        if (READY_LATENCY == 0) begin
            `uvm_warning(get_type_name(), "\n\tYou are using zero ready latency. It is supported only for R_TILE with full_speed_sequence.")
        end

        logic_vector_array_agent_cfg = new;
        logic_vector_agent_cfg = new;
        avst_agent_cfg = new;

        logic_vector_array_agent_cfg.active = m_config.active;
        logic_vector_agent_cfg.active = m_config.active;

        avst_agent_cfg.active = m_config.active;
        avst_agent_cfg.interface_name = m_config.interface_name;

        uvm_config_db #(uvm_logic_vector_array::config_item)::set(this, "m_logic_vector_array_agent", "m_config", logic_vector_array_agent_cfg);
        uvm_config_db #(uvm_logic_vector::config_item)::set(this, "m_logic_vector_agent", "m_config", logic_vector_agent_cfg);
        uvm_config_db #(uvm_avst::config_item)::set(this, "m_avst_agent", "m_config", avst_agent_cfg);

        uvm_logic_vector_array::monitor #(ITEM_WIDTH)::type_id::set_inst_override(monitor_logic_vector_array #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY)::get_type(), {this.get_full_name(), ".m_logic_vector_array_agent.*"});
        uvm_logic_vector::monitor#(META_WIDTH)::type_id::set_inst_override(monitor_logic_vector #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY)::get_type(), {this.get_full_name(), ".m_logic_vector_agent.*"});

        m_logic_vector_array_agent = uvm_logic_vector_array::agent#(ITEM_WIDTH)::type_id::create("m_logic_vector_array_agent", this);
        m_logic_vector_agent       = uvm_logic_vector::agent#(META_WIDTH)::type_id::create("m_logic_vector_agent", this);
        m_avst_agent               = uvm_avst::agent_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::type_id::create("m_avst_agent", this);

        if (m_config.active == UVM_ACTIVE) begin
            m_sequencer = sequencer_rx #(ITEM_WIDTH, META_WIDTH)::type_id::create("m_sequencer", this);
        end

        reset_sync = new();
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);

        monitor_logic_vector_array #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY) m_byte_arr_monitor;
        monitor_logic_vector #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY) m_logic_vector_monitor;

        $cast(m_byte_arr_monitor, m_logic_vector_array_agent.m_monitor);
        m_avst_agent.analysis_port.connect(m_byte_arr_monitor.analysis_export);
        analysis_port_data = m_logic_vector_array_agent.m_monitor.analysis_port;
        reset_sync.push_back(m_byte_arr_monitor.reset_sync);

        $cast(m_logic_vector_monitor, m_logic_vector_agent.m_monitor);
        m_logic_vector_monitor.meta_behav = m_config.meta_behav;
        m_avst_agent.analysis_port.connect(m_logic_vector_monitor.analysis_export);
        analysis_port_meta = m_logic_vector_agent.m_monitor.analysis_port;
        reset_sync.push_back(m_logic_vector_monitor.reset_sync);

        if (m_config.active == UVM_ACTIVE) begin
            m_sequencer.m_data = m_logic_vector_array_agent.m_sequencer;
            m_sequencer.m_meta = m_logic_vector_agent.m_sequencer;
            m_sequencer.meta_behav = m_config.meta_behav;
            reset_sync.push_back(m_avst_agent.m_sequencer.reset_sync);
            uvm_config_db #(sequencer_rx #(ITEM_WIDTH, META_WIDTH))::set(this, "m_avst_agent.m_sequencer", "hl_sqr", m_sequencer);
        end
    endfunction

    virtual task run_phase(uvm_phase phase);
        if (m_config.active == UVM_ACTIVE) begin
            sequence_lib_rx#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY) avst_seq;
            avst_seq = sequence_lib_rx#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY)::type_id::create("avst_seq", this);

            avst_seq.min_random_count = 20;
            avst_seq.max_random_count = 100;
            avst_seq.init_sequence(m_config.seq_cfg);

            forever begin
                int verbosity;

                verbosity = this.get_report_verbosity_level(UVM_INFO, "avst_seq");
                m_avst_agent.m_sequencer.set_report_verbosity_level(verbosity >= 300 ? verbosity - 300 : 0);

                if(!avst_seq.randomize()) `uvm_fatal(this.get_full_name(), "\n\tCannot randomize logic_vector_array_mfb rx_seq");
                avst_seq.start(m_avst_agent.m_sequencer);
            end
        end
    endtask

endclass


class env_tx #(int unsigned REGIONS, int unsigned REGION_SIZE, int unsigned BLOCK_SIZE, int unsigned ITEM_WIDTH, int unsigned META_WIDTH, int unsigned READY_LATENCY) extends uvm_env;
    `uvm_component_param_utils(uvm_logic_vector_array_avst::env_tx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY));

    //Access component
    uvm_avst::sequencer #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) m_sequencer;
    uvm_analysis_port #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)) analysis_port_data;
    uvm_analysis_port #(uvm_logic_vector::sequence_item#(META_WIDTH)) analysis_port_meta;
    uvm_reset::sync_cbs                                               reset_sync;

    // ------------------------------------------------------------------------
    // Definition of agents
    uvm_logic_vector_array::agent#(ITEM_WIDTH) m_logic_vector_array_agent;
    uvm_logic_vector_array::config_item logic_vector_array_agent_cfg;

    uvm_logic_vector::agent#(META_WIDTH) m_logic_vector_agent;
    uvm_logic_vector::config_item logic_vector_agent_cfg;

    uvm_avst::agent_tx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) m_avst_agent;
    uvm_avst::config_item avst_agent_cfg;

    config_item m_config;

    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);

        if(!uvm_config_db #(config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(get_type_name(), "Unable to get configuration object")
        end

        logic_vector_array_agent_cfg = new;
        logic_vector_agent_cfg       = new;
        avst_agent_cfg               = new;

        logic_vector_array_agent_cfg.active = m_config.active;
        logic_vector_agent_cfg.active       = UVM_PASSIVE;

        avst_agent_cfg.active         = m_config.active;
        avst_agent_cfg.interface_name = m_config.interface_name;

        uvm_config_db #(uvm_logic_vector_array::config_item)::set(this, "m_logic_vector_array_agent", "m_config", logic_vector_array_agent_cfg);
        uvm_config_db #(uvm_logic_vector::config_item)::set(this, "m_logic_vector_agent", "m_config", logic_vector_agent_cfg);
        uvm_config_db #(uvm_avst::config_item)::set(this, "m_avst_agent", "m_config", avst_agent_cfg);

        uvm_logic_vector_array::monitor#(ITEM_WIDTH)::type_id::set_inst_override(monitor_logic_vector_array #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY)::get_type(), {this.get_full_name(), ".m_logic_vector_array_agent.*"});
        uvm_logic_vector::monitor#(META_WIDTH)::type_id::set_inst_override(monitor_logic_vector #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY)::get_type(), {this.get_full_name(), ".m_logic_vector_agent.*"});

        m_logic_vector_array_agent = uvm_logic_vector_array::agent#(ITEM_WIDTH)::type_id::create("m_logic_vector_array_agent", this);
        m_logic_vector_agent       = uvm_logic_vector::agent#(META_WIDTH)::type_id::create("m_logic_vector_agent", this);
        m_avst_agent               = uvm_avst::agent_tx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::type_id::create("m_avst_agent", this);

        reset_sync = new();
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);

        monitor_logic_vector_array #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY) m_byte_arr_monitor;
        monitor_logic_vector #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY)       m_logic_vector_monitor;

        $cast(m_byte_arr_monitor, m_logic_vector_array_agent.m_monitor);
        m_avst_agent.analysis_port.connect(m_byte_arr_monitor.analysis_export);
        analysis_port_data = m_logic_vector_array_agent.m_monitor.analysis_port;
        reset_sync.push_back(m_byte_arr_monitor.reset_sync);

        $cast(m_logic_vector_monitor, m_logic_vector_agent.m_monitor);
        m_avst_agent.analysis_port.connect(m_logic_vector_monitor.analysis_export);
        m_logic_vector_monitor.meta_behav = m_config.meta_behav;
        analysis_port_meta = m_logic_vector_agent.m_monitor.analysis_port;
        reset_sync.push_back(m_logic_vector_monitor.reset_sync);

        m_sequencer = m_avst_agent.m_sequencer;
    endfunction
endclass

