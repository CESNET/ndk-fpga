//-- env.sv: Mfb environment
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// Definition of mfb environment
class env_rx #(int unsigned REGIONS, int unsigned REGION_SIZE, int unsigned BLOCK_SIZE, int unsigned META_WIDTH) extends uvm_env;
    `uvm_component_param_utils(uvm_byte_array_mfb::env_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, META_WIDTH));

    localparam  ITEM_WIDTH = 8;

    // ------------------------------------------------------------------------
    // Definition of agents
    sequencer_rx #(META_WIDTH) m_sequencer;
    uvm_analysis_port #(uvm_byte_array::sequence_item)                analysis_port_data;
    uvm_analysis_port #(uvm_logic_vector::sequence_item#(META_WIDTH)) analysis_port_meta;
    uvm_reset::sync_cbs            reset_sync;

    uvm_byte_array::agent m_byte_array_agent;
    uvm_byte_array::config_item byte_array_agent_cfg;

    uvm_logic_vector::agent#(META_WIDTH) m_logic_vector_agent;
    uvm_logic_vector::config_item logic_vector_agent_cfg;

    uvm_mfb::agent_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) m_mfb_agent;
    uvm_mfb::config_item mfb_agent_cfg;

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

        byte_array_agent_cfg = new;
        logic_vector_agent_cfg = new;
        mfb_agent_cfg = new;

        byte_array_agent_cfg.active = m_config.active;
        logic_vector_agent_cfg.active = m_config.active;

        mfb_agent_cfg.active = m_config.active;
        mfb_agent_cfg.interface_name = m_config.interface_name;

        uvm_config_db #(uvm_byte_array::config_item)::set(this, "m_byte_array_agent", "m_config", byte_array_agent_cfg);
        uvm_config_db #(uvm_logic_vector::config_item)::set(this, "m_logic_vector_agent", "m_config", logic_vector_agent_cfg);
        uvm_config_db #(uvm_mfb::config_item)::set(this, "m_mfb_agent", "m_config", mfb_agent_cfg);

        uvm_byte_array::monitor::type_id::set_inst_override(monitor_byte_array #(REGIONS, REGION_SIZE, BLOCK_SIZE, META_WIDTH)::get_type(), {this.get_full_name(), ".m_byte_array_agent.*"});
        uvm_logic_vector::monitor#(META_WIDTH)::type_id::set_inst_override(monitor_logic_vector #(REGIONS, REGION_SIZE, BLOCK_SIZE, META_WIDTH)::get_type(), {this.get_full_name(), ".m_logic_vector_agent.*"});

        m_byte_array_agent = uvm_byte_array::agent::type_id::create("m_byte_array_agent", this);
        m_logic_vector_agent = uvm_logic_vector::agent#(META_WIDTH)::type_id::create("m_logic_vector_agent", this);
        m_mfb_agent        = uvm_mfb::agent_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::type_id::create("m_mfb_agent", this);

        if (m_config.active == UVM_ACTIVE) begin
            m_sequencer = sequencer_rx #(META_WIDTH)::type_id::create("m_sequencer", this);
        end

        reset_sync = new();
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);

        monitor_byte_array #(REGIONS, REGION_SIZE, BLOCK_SIZE, META_WIDTH) m_byte_arr_monitor;
        monitor_logic_vector #(REGIONS, REGION_SIZE, BLOCK_SIZE, META_WIDTH) m_logic_vector_monitor;

        $cast(m_byte_arr_monitor, m_byte_array_agent.m_monitor);
        m_mfb_agent.analysis_port.connect(m_byte_arr_monitor.analysis_export);
        analysis_port_data = m_byte_array_agent.m_monitor.analysis_port;
        reset_sync.push_back(m_byte_arr_monitor.reset_sync);

        $cast(m_logic_vector_monitor, m_logic_vector_agent.m_monitor);
        m_logic_vector_monitor.meta_behav = m_config.meta_behav;
        m_mfb_agent.analysis_port.connect(m_logic_vector_monitor.analysis_export);
        analysis_port_meta = m_logic_vector_agent.m_monitor.analysis_port;
        reset_sync.push_back(m_logic_vector_monitor.reset_sync);

        if (m_config.active == UVM_ACTIVE) begin
            m_sequencer.m_data     = m_byte_array_agent.m_sequencer;
            m_sequencer.m_meta     = m_logic_vector_agent.m_sequencer;
            m_sequencer.meta_behav = m_config.meta_behav;
            reset_sync.push_back(m_mfb_agent.m_sequencer.reset_sync);
            reset_sync.push_back(m_sequencer.m_data.reset_sync);
            //reset_sync.push_back(m_sequencer.m_meta.reset_sync);
            uvm_config_db #(sequencer_rx #(META_WIDTH))::set(this, "m_mfb_agent.m_sequencer", "hl_sqr", m_sequencer);
        end
    endfunction

    virtual task run_phase(uvm_phase phase);
        if (m_config.active == UVM_ACTIVE) begin
            uvm_byte_array_mfb::sequence_lib_rx#(REGIONS, REGION_SIZE, BLOCK_SIZE, META_WIDTH) mfb_seq;

            mfb_seq = uvm_byte_array_mfb::sequence_lib_rx#(REGIONS, REGION_SIZE, BLOCK_SIZE, META_WIDTH)::type_id::create("mfb_seq", this);
            mfb_seq.min_random_count = 20;
            mfb_seq.max_random_count = 100;
            mfb_seq.init_sequence(m_config.seq_cfg);

            forever begin
                //mfb_seq.set_starting_phase(phase);
                if(!mfb_seq.randomize()) `uvm_fatal(this.get_full_name(), "\n\tCannot randomize byte_array_mfb rx_seq");
                mfb_seq.start(m_mfb_agent.m_sequencer);
            end
        end
    endtask

endclass


class env_tx #(int unsigned REGIONS, int unsigned REGION_SIZE, int unsigned BLOCK_SIZE, int unsigned META_WIDTH) extends uvm_env;
    `uvm_component_param_utils(uvm_byte_array_mfb::env_tx #(REGIONS, REGION_SIZE, BLOCK_SIZE, META_WIDTH));

    localparam  ITEM_WIDTH = 8;

    //Access component
    uvm_mfb::sequencer #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) m_sequencer;
    uvm_analysis_port #(uvm_byte_array::sequence_item)                analysis_port_data;
    uvm_analysis_port #(uvm_logic_vector::sequence_item#(META_WIDTH)) analysis_port_meta;
    uvm_reset::sync_cbs                                               reset_sync;

    // ------------------------------------------------------------------------
    // Definition of agents
    uvm_byte_array::agent m_byte_array_agent;
    uvm_byte_array::config_item byte_array_agent_cfg;

    uvm_logic_vector::agent#(META_WIDTH) m_logic_vector_agent;
    uvm_logic_vector::config_item logic_vector_agent_cfg;

    uvm_mfb::agent_tx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) m_mfb_agent;
    uvm_mfb::config_item mfb_agent_cfg;

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

        byte_array_agent_cfg = new;
        logic_vector_agent_cfg = new;
        mfb_agent_cfg = new;

        byte_array_agent_cfg.active = m_config.active;
        logic_vector_agent_cfg.active = UVM_PASSIVE;

        mfb_agent_cfg.active = m_config.active;
        mfb_agent_cfg.interface_name = m_config.interface_name;

        uvm_config_db #(uvm_byte_array::config_item)::set(this, "m_byte_array_agent", "m_config", byte_array_agent_cfg);
        uvm_config_db #(uvm_logic_vector::config_item)::set(this, "m_logic_vector_agent", "m_config", logic_vector_agent_cfg);
        uvm_config_db #(uvm_mfb::config_item)::set(this, "m_mfb_agent", "m_config", mfb_agent_cfg);

        uvm_byte_array::monitor::type_id::set_inst_override(monitor_byte_array #(REGIONS, REGION_SIZE, BLOCK_SIZE, META_WIDTH)::get_type(), {this.get_full_name(), ".m_byte_array_agent.*"});
        uvm_logic_vector::monitor#(META_WIDTH)::type_id::set_inst_override(monitor_logic_vector #(REGIONS, REGION_SIZE, BLOCK_SIZE, META_WIDTH)::get_type(), {this.get_full_name(), ".m_logic_vector_agent.*"});

        m_byte_array_agent = uvm_byte_array::agent::type_id::create("m_byte_array_agent", this);
        m_logic_vector_agent = uvm_logic_vector::agent#(META_WIDTH)::type_id::create("m_logic_vector_agent", this);
        m_mfb_agent        = uvm_mfb::agent_tx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::type_id::create("m_mfb_agent", this);

        reset_sync = new();
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);

        monitor_byte_array #(REGIONS, REGION_SIZE, BLOCK_SIZE, META_WIDTH)   m_byte_arr_monitor;
        monitor_logic_vector #(REGIONS, REGION_SIZE, BLOCK_SIZE, META_WIDTH) m_logic_vector_monitor;

        $cast(m_byte_arr_monitor, m_byte_array_agent.m_monitor);
        m_mfb_agent.analysis_port.connect(m_byte_arr_monitor.analysis_export);
        analysis_port_data = m_byte_array_agent.m_monitor.analysis_port;
        reset_sync.push_back(m_byte_arr_monitor.reset_sync);

        $cast(m_logic_vector_monitor, m_logic_vector_agent.m_monitor);
        m_mfb_agent.analysis_port.connect(m_logic_vector_monitor.analysis_export);
        m_logic_vector_monitor.meta_behav = m_config.meta_behav;
        analysis_port_meta = m_logic_vector_agent.m_monitor.analysis_port;
        reset_sync.push_back(m_logic_vector_monitor.reset_sync);

        m_sequencer = m_mfb_agent.m_sequencer;
    endfunction
endclass

