//-- env.sv
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class env #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, CHANNELS, PKT_SIZE_MAX) extends uvm_env;
    `uvm_component_param_utils(uvm_dma_ll_rx::env #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, CHANNELS, PKT_SIZE_MAX));

    localparam MFB_META_WIDTH = 24 + $clog2(PKT_SIZE_MAX+1) + $clog2(CHANNELS);

    //top sequencer
    sequencer#(ITEM_WIDTH)                      m_sequencer;
    driver#(ITEM_WIDTH, CHANNELS, PKT_SIZE_MAX) m_driver;

    //toplevel
    uvm_logic_vector_array::agent#(ITEM_WIDTH)   m_logic_vector_array_agent;
    //low level
    uvm_logic_vector_array_mfb::env_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, MFB_META_WIDTH) m_env_rx;
    //implementa later
    uvm_reset::sync_cbs            reset_sync;
    //configuration
    config_item m_config;

    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function int unsigned used();
        return m_driver.used();
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);
        uvm_logic_vector_array::config_item     m_logic_vector_array_agent_cfg;
        uvm_logic_vector_array_mfb::config_item m_env_rx_cfg;

        if(!uvm_config_db #(config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(get_type_name(), "Unable to get configuration object")
        end

        //TOP level agent
        m_logic_vector_array_agent_cfg = new();
        m_logic_vector_array_agent_cfg.active = m_config.active;

        uvm_config_db #(uvm_logic_vector_array::config_item)::set(this, "m_logic_vector_array_agent", "m_config", m_logic_vector_array_agent_cfg);

        m_logic_vector_array_agent   = uvm_logic_vector_array::agent#(ITEM_WIDTH)::type_id::create("m_logic_vector_array_agent", this);
        // LOW level agent
        m_env_rx_cfg = new;
        m_env_rx_cfg.active  = m_config.active;
        m_env_rx_cfg.interface_name = m_config.interface_name;
        m_env_rx_cfg.meta_behav = uvm_logic_vector_array_mfb::config_item::META_SOF;

        uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, "m_env_rx", "m_config", m_env_rx_cfg);
        m_env_rx  = uvm_logic_vector_array_mfb::env_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, MFB_META_WIDTH)::type_id::create("m_env_rx", this);

        if (m_config.active == UVM_ACTIVE) begin
            m_sequencer = sequencer#(ITEM_WIDTH)::type_id::create("m_sequencer", this);
            m_driver    = driver#(ITEM_WIDTH, CHANNELS, PKT_SIZE_MAX)::type_id::create(" m_driver", this);
        end

        reset_sync = new();
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);
        if (m_config.active == UVM_ACTIVE) begin
            m_sequencer.m_data_sqcr = m_logic_vector_array_agent.m_sequencer;

            m_driver.seq_item_port_logic_vector_array.connect(m_logic_vector_array_agent.m_sequencer.seq_item_export);
        end

        reset_sync.push_back(m_env_rx.reset_sync);
    endfunction

    virtual task run_phase(uvm_phase phase);
        if (m_config.active == UVM_ACTIVE) begin
            logic_vector_sequence#(MFB_META_WIDTH)   logic_vector_seq;
            logic_vector_array_sequence#(ITEM_WIDTH) logic_vector_array_seq;

            logic_vector_seq = logic_vector_sequence#(MFB_META_WIDTH)::type_id::create("logic_vector_seq", this);
            logic_vector_seq.tr_export = m_driver.logic_vector_export;
            logic_vector_seq.randomize();
            logic_vector_array_seq   = logic_vector_array_sequence#(ITEM_WIDTH)::type_id::create("logic_vector_array_seq", this);
            logic_vector_array_seq.tr_export   = m_driver.logic_vector_array_export;
            logic_vector_array_seq.randomize();

            fork
                logic_vector_seq.start(m_env_rx.m_sequencer.m_meta);
                logic_vector_array_seq.start(m_env_rx.m_sequencer.m_data);
            join
        end
    endtask
endclass

