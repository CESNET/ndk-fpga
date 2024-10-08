//-- env.sv: AXI environment
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// Definition of axi environment
class env_rx #(int unsigned DATA_WIDTH, int unsigned TUSER_WIDTH, int unsigned ITEM_WIDTH, int unsigned REGIONS, int unsigned BLOCK_SIZE, int unsigned STRADDLING) extends uvm_env;
    `uvm_component_param_utils(uvm_logic_vector_array_axi::env_rx #(DATA_WIDTH, TUSER_WIDTH, ITEM_WIDTH, REGIONS, BLOCK_SIZE, STRADDLING));

    // ------------------------------------------------------------------------
    // Definition of agents
    sequencer_rx #(ITEM_WIDTH)                                              m_sequencer;
    uvm_analysis_port #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)) analysis_port_data;
    uvm_analysis_port #(uvm_logic_vector::sequence_item#(TUSER_WIDTH))      analysis_port_meta;
    uvm_reset::sync_cbs                                                     reset_sync;

    uvm_logic_vector_array::agent#(ITEM_WIDTH) m_logic_vector_array_agent;
    uvm_logic_vector_array::config_item        logic_vector_array_agent_cfg;

    uvm_logic_vector::agent#(TUSER_WIDTH) m_logic_vector_agent;
    uvm_logic_vector::config_item         logic_vector_agent_cfg;

    uvm_axi::agent_rx #(DATA_WIDTH, TUSER_WIDTH, REGIONS) m_axi_agent;
    uvm_axi::config_item                                  axi_agent_cfg;

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
        axi_agent_cfg                = new;

        logic_vector_array_agent_cfg.active = m_config.active;
        logic_vector_agent_cfg.active       = UVM_PASSIVE;

        axi_agent_cfg.active         = m_config.active;
        axi_agent_cfg.interface_name = m_config.interface_name;

        uvm_config_db #(uvm_logic_vector_array::config_item)::set(this, "m_logic_vector_array_agent", "m_config", logic_vector_array_agent_cfg);
        uvm_config_db #(uvm_logic_vector::config_item)::set(this, "m_logic_vector_agent", "m_config", logic_vector_agent_cfg);
        uvm_config_db #(uvm_axi::config_item)::set(this, "m_axi_agent", "m_config", axi_agent_cfg);

        uvm_logic_vector_array::monitor #(ITEM_WIDTH)::type_id::set_inst_override(monitor_logic_vector_array #(DATA_WIDTH, TUSER_WIDTH, ITEM_WIDTH, REGIONS, BLOCK_SIZE, STRADDLING)::get_type(), {this.get_full_name(), ".m_logic_vector_array_agent.*"});
        uvm_logic_vector::monitor#(TUSER_WIDTH)::type_id::set_inst_override(monitor_logic_vector #(DATA_WIDTH, TUSER_WIDTH, ITEM_WIDTH, REGIONS, BLOCK_SIZE, STRADDLING)::get_type(), {this.get_full_name(), ".m_logic_vector_agent.*"});

        m_logic_vector_array_agent = uvm_logic_vector_array::agent#(ITEM_WIDTH)::type_id::create("m_logic_vector_array_agent", this);
        m_logic_vector_agent       = uvm_logic_vector::agent#(TUSER_WIDTH)::type_id::create("m_logic_vector_agent", this);
        m_axi_agent                = uvm_axi::agent_rx #(DATA_WIDTH, TUSER_WIDTH, REGIONS)::type_id::create("m_axi_agent", this);

        if (m_config.active == UVM_ACTIVE) begin
            m_sequencer = sequencer_rx #(ITEM_WIDTH)::type_id::create("m_sequencer", this);
        end

        reset_sync = new();
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);

        monitor_logic_vector_array #(DATA_WIDTH, TUSER_WIDTH, ITEM_WIDTH, REGIONS, BLOCK_SIZE, STRADDLING) m_logic_vector_arr_monitor;
        monitor_logic_vector #(DATA_WIDTH, TUSER_WIDTH, ITEM_WIDTH, REGIONS, BLOCK_SIZE, STRADDLING)       m_logic_vector_monitor;

        $cast(m_logic_vector_arr_monitor, m_logic_vector_array_agent.m_monitor);
        m_axi_agent.analysis_port.connect(m_logic_vector_arr_monitor.analysis_export);
        analysis_port_data = m_logic_vector_array_agent.m_monitor.analysis_port;
        reset_sync.push_back(m_logic_vector_arr_monitor.reset_sync);

        $cast(m_logic_vector_monitor, m_logic_vector_agent.m_monitor);
        m_logic_vector_monitor.meta_behav = m_config.meta_behav;
        m_axi_agent.analysis_port.connect(m_logic_vector_monitor.analysis_export);
        analysis_port_meta = m_logic_vector_agent.m_monitor.analysis_port;
        reset_sync.push_back(m_logic_vector_monitor.reset_sync);

        if (m_config.active == UVM_ACTIVE) begin
            m_sequencer.m_data = m_logic_vector_array_agent.m_sequencer;
            reset_sync.push_back(m_axi_agent.m_sequencer.reset_sync);
            uvm_config_db #(sequencer_rx #(ITEM_WIDTH))::set(this, "m_axi_agent.m_sequencer", "hl_sqr", m_sequencer);
        end
    endfunction

    virtual task run_phase(uvm_phase phase);
        if (m_config.active == UVM_ACTIVE) begin
            sequence_lib_rx#(DATA_WIDTH, TUSER_WIDTH, REGIONS, BLOCK_SIZE, STRADDLING) axi_seq;

            axi_seq                  = sequence_lib_rx#(DATA_WIDTH, TUSER_WIDTH, REGIONS, BLOCK_SIZE, STRADDLING)::type_id::create("axi_seq", this);
            axi_seq.cfg              = m_config.seq_cfg;
            axi_seq.min_random_count = 20;
            axi_seq.max_random_count = 100;
            axi_seq.init_sequence();

            forever begin
                if(!axi_seq.randomize()) `uvm_fatal(this.get_full_name(), "\n\tCannot randomize logic_vector_array_axi rx_seq");
                axi_seq.start(m_axi_agent.m_sequencer);
            end
        end
    endtask

endclass


class env_tx #(int unsigned DATA_WIDTH, int unsigned TUSER_WIDTH, int unsigned ITEM_WIDTH, int unsigned REGIONS, int unsigned BLOCK_SIZE, int unsigned STRADDLING) extends uvm_env;
    `uvm_component_param_utils(uvm_logic_vector_array_axi::env_tx #(DATA_WIDTH, TUSER_WIDTH, ITEM_WIDTH, REGIONS, BLOCK_SIZE, STRADDLING));

    //Access component
    uvm_axi::sequencer #(DATA_WIDTH, TUSER_WIDTH, REGIONS)                  m_sequencer;
    uvm_analysis_port #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)) analysis_port_data;
    uvm_analysis_port #(uvm_logic_vector::sequence_item#(TUSER_WIDTH))      analysis_port_meta;
    uvm_reset::sync_cbs                                                     reset_sync;

    // ------------------------------------------------------------------------
    // Definition of agents
    uvm_logic_vector_array::agent#(ITEM_WIDTH) m_logic_vector_array_agent;
    uvm_logic_vector_array::config_item        logic_vector_array_agent_cfg;

    uvm_logic_vector::agent#(TUSER_WIDTH) m_logic_vector_agent;
    uvm_logic_vector::config_item         logic_vector_agent_cfg;

    uvm_axi::agent_tx #(DATA_WIDTH, TUSER_WIDTH, REGIONS) m_axi_agent;
    uvm_axi::config_item                                  axi_agent_cfg;

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
        axi_agent_cfg                = new;

        logic_vector_array_agent_cfg.active = m_config.active;
        logic_vector_agent_cfg.active       = UVM_PASSIVE;

        axi_agent_cfg.active         = m_config.active;
        axi_agent_cfg.interface_name = m_config.interface_name;

        uvm_config_db #(uvm_logic_vector_array::config_item)::set(this, "m_logic_vector_array_agent", "m_config", logic_vector_array_agent_cfg);
        uvm_config_db #(uvm_logic_vector::config_item)::set(this, "m_logic_vector_agent", "m_config", logic_vector_agent_cfg);
        uvm_config_db #(uvm_axi::config_item)::set(this, "m_axi_agent", "m_config", axi_agent_cfg);

        uvm_logic_vector_array::monitor#(ITEM_WIDTH)::type_id::set_inst_override(monitor_logic_vector_array #(DATA_WIDTH, TUSER_WIDTH, ITEM_WIDTH, REGIONS, BLOCK_SIZE, STRADDLING)::get_type(), {this.get_full_name(), ".m_logic_vector_array_agent.*"});
        uvm_logic_vector::monitor#(TUSER_WIDTH)::type_id::set_inst_override(monitor_logic_vector #(DATA_WIDTH, TUSER_WIDTH, ITEM_WIDTH, REGIONS, BLOCK_SIZE, STRADDLING)::get_type(), {this.get_full_name(), ".m_logic_vector_agent.*"});

        m_logic_vector_array_agent = uvm_logic_vector_array::agent#(ITEM_WIDTH)::type_id::create("m_logic_vector_array_agent", this);
        m_logic_vector_agent       = uvm_logic_vector::agent#(TUSER_WIDTH)::type_id::create("m_logic_vector_agent", this);
        m_axi_agent                = uvm_axi::agent_tx #(DATA_WIDTH, TUSER_WIDTH, REGIONS)::type_id::create("m_axi_agent", this);

        reset_sync = new();
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);

        monitor_logic_vector_array #(DATA_WIDTH, TUSER_WIDTH, ITEM_WIDTH, REGIONS, BLOCK_SIZE, STRADDLING) m_logic_vector_arr_monitor;
        monitor_logic_vector #(DATA_WIDTH, TUSER_WIDTH, ITEM_WIDTH, REGIONS, BLOCK_SIZE, STRADDLING)       m_logic_vector_monitor;

        $cast(m_logic_vector_arr_monitor, m_logic_vector_array_agent.m_monitor);
        m_axi_agent.analysis_port.connect(m_logic_vector_arr_monitor.analysis_export);
        analysis_port_data = m_logic_vector_array_agent.m_monitor.analysis_port;
        reset_sync.push_back(m_logic_vector_arr_monitor.reset_sync);

        $cast(m_logic_vector_monitor, m_logic_vector_agent.m_monitor);
        m_logic_vector_monitor.meta_behav = m_config.meta_behav;
        m_axi_agent.analysis_port.connect(m_logic_vector_monitor.analysis_export);
        analysis_port_meta = m_logic_vector_agent.m_monitor.analysis_port;
        reset_sync.push_back(m_logic_vector_monitor.reset_sync);

        m_sequencer = m_axi_agent.m_sequencer;
    endfunction
endclass

