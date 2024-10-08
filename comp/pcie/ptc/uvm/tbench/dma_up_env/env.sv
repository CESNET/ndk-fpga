//-- env.sv
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class env #(DMA_MVB_UP_ITEMS, DMA_MFB_UP_REGIONS, MFB_UP_REG_SIZE, MFB_UP_BLOCK_SIZE, MFB_UP_ITEM_WIDTH, DMA_PORTS) extends uvm_env;
    `uvm_component_param_utils(uvm_dma_up::env #(DMA_MVB_UP_ITEMS, DMA_MFB_UP_REGIONS, MFB_UP_REG_SIZE, MFB_UP_BLOCK_SIZE, MFB_UP_ITEM_WIDTH, DMA_PORTS));

    localparam MFB_META_WIDTH = sv_dma_bus_pack::DMA_REQUEST_LENGTH_W   + sv_dma_bus_pack::DMA_REQUEST_TYPE_W + sv_dma_bus_pack::DMA_REQUEST_FIRSTIB_W +
                                sv_dma_bus_pack::DMA_REQUEST_LASTIB_W   + sv_dma_bus_pack::DMA_REQUEST_TAG_W + sv_dma_bus_pack::DMA_REQUEST_UNITID_W   +
                                sv_dma_bus_pack::DMA_REQUEST_GLOBAL_W   + sv_dma_bus_pack::DMA_REQUEST_VFID_W + sv_dma_bus_pack::DMA_REQUEST_PASID_W   +
                                sv_dma_bus_pack::DMA_REQUEST_PASIDVLD_W + sv_dma_bus_pack::DMA_REQUEST_RELAXED_W;

    // TOP sequencer
    sequencer                         m_sequencer;
    driver #(DMA_PORTS) m_driver;
    // TOP level
    uvm_logic_vector_array::agent#(32) m_byte_array_agent;
    uvm_ptc_info::agent                m_info_agent;
    // Low level
    uvm_logic_vector_array_mfb::env_rx #(DMA_MFB_UP_REGIONS, MFB_UP_REG_SIZE, MFB_UP_BLOCK_SIZE, 32, 0) m_env_up_mfb;
    uvm_logic_vector_mvb::env_rx #(DMA_MVB_UP_ITEMS, sv_dma_bus_pack::DMA_UPHDR_WIDTH)                                   m_env_up_mvb;
    // Implement later
    uvm_reset::sync_cbs reset_sync;
    // Configuration
    config_item #(DMA_PORTS) m_config;

    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);
        uvm_ptc_info::config_item               m_info_agent_cfg;
        uvm_logic_vector_array::config_item     m_byte_array_agent_cfg;
        uvm_logic_vector_array_mfb::config_item m_env_up_mfb_cfg;
        uvm_logic_vector_mvb::config_item       m_env_up_mvb_cfg;

        if(!uvm_config_db #(config_item #(DMA_PORTS))::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(get_type_name(), "Unable to get configuration object")
        end

        // TOP level agent
        m_info_agent_cfg              = new();
        m_byte_array_agent_cfg        = new();
        m_info_agent_cfg.active       = m_config.active;
        m_byte_array_agent_cfg.active = m_config.active;

        uvm_config_db #(uvm_ptc_info::config_item)::set(this, "m_info_agent", "m_config", m_info_agent_cfg);
        uvm_config_db #(uvm_logic_vector_array::config_item)::set(this, "m_byte_array_agent", "m_config", m_byte_array_agent_cfg);

        m_info_agent       = uvm_ptc_info::agent::type_id::create("m_info_agent",         this);
        m_byte_array_agent = uvm_logic_vector_array::agent#(32)::type_id::create("m_byte_array_agent", this);
        // Low level agent
        m_env_up_mfb_cfg                = new;
        m_env_up_mfb_cfg.active         = m_config.active;
        m_env_up_mfb_cfg.interface_name = {m_config.interface_name, $sformatf("_mfb_%d", m_config.port)};

        m_env_up_mvb_cfg                = new;
        m_env_up_mvb_cfg.active         = m_config.active;
        m_env_up_mvb_cfg.interface_name = {m_config.interface_name, $sformatf("_mvb_%d", m_config.port)};

        uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, "m_env_up_mfb", "m_config", m_env_up_mfb_cfg);
        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "m_env_up_mvb", "m_config", m_env_up_mvb_cfg);
        m_env_up_mfb  = uvm_logic_vector_array_mfb::env_rx #(DMA_MFB_UP_REGIONS, MFB_UP_REG_SIZE, MFB_UP_BLOCK_SIZE, 32, 0)::type_id::create("m_env_up_mfb", this);
        m_env_up_mvb  = uvm_logic_vector_mvb::env_rx #(DMA_MVB_UP_ITEMS, sv_dma_bus_pack::DMA_UPHDR_WIDTH)::type_id::create("m_env_up_mvb", this);

        if (m_config.active == UVM_ACTIVE) begin
            m_sequencer   = sequencer::type_id::create("m_sequencer", this);
            m_driver      = driver #(DMA_PORTS)::type_id::create("m_driver", this);
            m_driver.port = m_config.port;
        end

        reset_sync = new();
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);
        if (m_config.active == UVM_ACTIVE) begin
            m_sequencer.m_info = m_info_agent.m_sequencer;
            m_sequencer.m_data = m_byte_array_agent.m_sequencer;

            m_driver.seq_item_port_info.connect(m_info_agent.m_sequencer.seq_item_export);
            m_driver.seq_item_port_logic_vector_array.connect(m_byte_array_agent.m_sequencer.seq_item_export);
        end

        //reset_sync.push_back(m_env_up_mfb.reset_sync);
        //reset_sync.push_back(m_env_up_mvb.reset_sync);
    endfunction

    virtual task run_phase(uvm_phase phase);
        if (m_config.active == UVM_ACTIVE) begin
            logic_vector_sequence #(MFB_META_WIDTH) logic_vector_seq;
            logic_vector_array_sequence             logic_vector_array_seq;

            logic_vector_seq           = logic_vector_sequence #(MFB_META_WIDTH)::type_id::create("logic_vector_seq", this);
            logic_vector_seq.tr_export = m_driver.logic_vector_export;
            logic_vector_seq.randomize();
            logic_vector_array_seq           = logic_vector_array_sequence::type_id::create("logic_vector_array_seq", this);
            logic_vector_array_seq.tr_export = m_driver.logic_vector_array_export;
            logic_vector_array_seq.randomize();

            fork
                logic_vector_seq.start(m_env_up_mvb.m_sequencer);
                logic_vector_array_seq.start(m_env_up_mfb.m_sequencer.m_data);
            join_none
        end
    endtask
endclass

