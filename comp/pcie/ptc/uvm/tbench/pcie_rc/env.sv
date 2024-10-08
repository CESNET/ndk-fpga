//-- env.sv
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class env #(MFB_DOWN_REGIONS, MFB_DOWN_REG_SIZE, MFB_DOWN_BLOCK_SIZE, MFB_DOWN_ITEM_WIDTH, PCIE_UPHDR_WIDTH, PCIE_DOWNHDR_WIDTH, PCIE_PREFIX_WIDTH, RC_TDATA_WIDTH, RC_TUSER_WIDTH, RQ_TUSER_WIDTH, RCB_SIZE, CLK_PERIOD, string DEVICE) extends uvm_env;
    `uvm_component_param_utils(uvm_pcie_rc::env #(MFB_DOWN_REGIONS, MFB_DOWN_REG_SIZE, MFB_DOWN_BLOCK_SIZE, MFB_DOWN_ITEM_WIDTH, PCIE_UPHDR_WIDTH, PCIE_DOWNHDR_WIDTH, PCIE_PREFIX_WIDTH, RC_TDATA_WIDTH, RC_TUSER_WIDTH, RQ_TUSER_WIDTH, RCB_SIZE, CLK_PERIOD, DEVICE));

    localparam MFB_META_WIDTH = sv_dma_bus_pack::DMA_COMPLETION_LENGTH_W + sv_dma_bus_pack::DMA_COMPLETION_COMPLETED_W + sv_dma_bus_pack::DMA_COMPLETION_TAG_W +
                                sv_dma_bus_pack::DMA_COMPLETION_UNITID_W;
    localparam HDR_USER_WIDTH = (DEVICE == "STRATIX10" || DEVICE == "AGILEX") ? PCIE_UPHDR_WIDTH : PCIE_UPHDR_WIDTH+RQ_TUSER_WIDTH;

    // TOP sequencer
    sequencer #(DEVICE)                 m_sequencer;
    monitor #((HDR_USER_WIDTH), DEVICE) m_monitor;
    // TOP level
    uvm_logic_vector_array::agent#(32)         m_byte_array_agent;
    uvm_logic_vector::agent#(PCIE_UPHDR_WIDTH) m_logic_vector_agent;
    uvm_ptc_info_rc::agent#(DEVICE)            m_info_rc_agent;
    // Low level
    uvm_logic_vector_array_mfb::env_rx #(MFB_DOWN_REGIONS, MFB_DOWN_REG_SIZE, MFB_DOWN_BLOCK_SIZE, MFB_DOWN_ITEM_WIDTH, PCIE_DOWNHDR_WIDTH) m_env_rc_mfb;
    uvm_logic_vector_mvb::env_rx #(MFB_DOWN_REGIONS, PCIE_PREFIX_WIDTH)                                                                 m_env_rc_prefix_mvb;
    uvm_logic_vector_array_axi::env_rx #(RC_TDATA_WIDTH, RC_TUSER_WIDTH, MFB_DOWN_ITEM_WIDTH, MFB_DOWN_REGIONS, MFB_DOWN_BLOCK_SIZE, 1) m_env_rc_axi;

    uvm_pcie_rc::tr_planner #(HDR_USER_WIDTH, RQ_TUSER_WIDTH, PCIE_DOWNHDR_WIDTH, RCB_SIZE, CLK_PERIOD, DEVICE) tr_plan;
    // Implement later
    uvm_reset::sync_cbs reset_sync;
    // Configuration
    config_item m_config;

    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);
        uvm_ptc_info_rc::config_item            m_info_rc_agent_cfg;
        uvm_logic_vector_array::config_item     m_byte_array_agent_cfg;
        uvm_logic_vector::config_item           m_logic_vector_agent_cfg;
        uvm_logic_vector_array_mfb::config_item m_env_rc_mfb_cfg;
        uvm_logic_vector_mvb::config_item       m_env_rc_prefix_mvb_cfg;
        uvm_logic_vector_array_axi::config_item m_env_rc_axi_cfg;

        if(!uvm_config_db #(config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(get_type_name(), "Unable to get configuration object")
        end

        tr_plan = uvm_pcie_rc::tr_planner #(HDR_USER_WIDTH, RQ_TUSER_WIDTH, PCIE_DOWNHDR_WIDTH, RCB_SIZE, CLK_PERIOD, DEVICE)::type_id::create("tr_plan", this);
        // TOP level agent
        m_info_rc_agent_cfg             = new();
        m_byte_array_agent_cfg          = new();
        m_logic_vector_agent_cfg        = new();
        m_info_rc_agent_cfg.active      = m_config.active;
        m_byte_array_agent_cfg.active   = m_config.active;
        m_logic_vector_agent_cfg.active = m_config.active;

        uvm_config_db #(uvm_ptc_info_rc::config_item)::set(this, "m_info_rc_agent",       "m_config", m_info_rc_agent_cfg);
        uvm_config_db #(uvm_logic_vector_array::config_item)::set(this, "m_byte_array_agent", "m_config", m_byte_array_agent_cfg);
        uvm_config_db #(uvm_logic_vector::config_item)::set(this, "m_logic_vector_agent", "m_config", m_logic_vector_agent_cfg);

        m_info_rc_agent      = uvm_ptc_info_rc::agent #(DEVICE)::type_id::create("m_info_rc_agent", this);
        m_byte_array_agent   = uvm_logic_vector_array::agent#(32)::type_id::create("m_byte_array_agent", this);
        m_logic_vector_agent = uvm_logic_vector::agent#(PCIE_UPHDR_WIDTH)::type_id::create("m_logic_vector_agent", this);
        // Low level agent
        m_env_rc_mfb_cfg                = new;
        m_env_rc_mfb_cfg.active         = m_config.active;
        m_env_rc_mfb_cfg.interface_name = m_config.interface_name_mfb;
        m_env_rc_mfb_cfg.meta_behav     = uvm_logic_vector_array_mfb::config_item::META_SOF; // meta with sof

        m_env_rc_prefix_mvb_cfg                = new;
        m_env_rc_prefix_mvb_cfg.active         = m_config.active;
        m_env_rc_prefix_mvb_cfg.interface_name = m_config.interface_name_mvb_pref;

        m_env_rc_axi_cfg                       = new;
        m_env_rc_axi_cfg.active                = m_config.active;
        m_env_rc_axi_cfg.interface_name        = m_config.interface_name_axi;
        m_env_rc_axi_cfg.meta_behav            = uvm_logic_vector_array_axi::config_item::META_NONE;

        uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, "m_env_rc_mfb", "m_config", m_env_rc_mfb_cfg);
        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "m_env_rc_prefix_mvb", "m_config", m_env_rc_prefix_mvb_cfg);
        uvm_config_db #(uvm_logic_vector_array_axi::config_item)::set(this, "m_env_rc_axi", "m_config", m_env_rc_axi_cfg);
        m_env_rc_mfb        = uvm_logic_vector_array_mfb::env_rx #(MFB_DOWN_REGIONS, MFB_DOWN_REG_SIZE, MFB_DOWN_BLOCK_SIZE, MFB_DOWN_ITEM_WIDTH, PCIE_DOWNHDR_WIDTH)::type_id::create("m_env_rc_mfb", this);
        m_env_rc_prefix_mvb = uvm_logic_vector_mvb::env_rx #(MFB_DOWN_REGIONS, PCIE_PREFIX_WIDTH)::type_id::create("m_env_rc_prefix_mvb", this);
        m_env_rc_axi = uvm_logic_vector_array_axi::env_rx #(RC_TDATA_WIDTH, RC_TUSER_WIDTH, MFB_DOWN_ITEM_WIDTH, MFB_DOWN_REGIONS, MFB_DOWN_BLOCK_SIZE, 1)::type_id::create("m_env_rc_axi", this);

        m_monitor = monitor #((HDR_USER_WIDTH), DEVICE)::type_id::create("m_monitor", this);

        if (m_config.active == UVM_ACTIVE) begin
            m_sequencer = sequencer #(DEVICE)::type_id::create("m_sequencer", this);
        end

        reset_sync = new();
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);
        m_monitor.analysis_port.connect(tr_plan.analysis_imp);

        //reset_sync.push_back(m_env_rc_mfb.reset_sync);
        //reset_sync.push_back(m_env_rc_mvb.reset_sync);
    endfunction

    virtual task run_phase(uvm_phase phase);
        if (m_config.active == UVM_ACTIVE) begin
            logic_vector_sequence #(PCIE_DOWNHDR_WIDTH, PCIE_UPHDR_WIDTH, RQ_TUSER_WIDTH, RCB_SIZE, CLK_PERIOD, DEVICE) logic_vector_seq;
            byte_array_sequence#(PCIE_UPHDR_WIDTH, PCIE_DOWNHDR_WIDTH, RQ_TUSER_WIDTH, RCB_SIZE, CLK_PERIOD, DEVICE)    byte_array_seq;

            logic_vector_seq         = logic_vector_sequence #(PCIE_DOWNHDR_WIDTH, PCIE_UPHDR_WIDTH, RQ_TUSER_WIDTH, RCB_SIZE, CLK_PERIOD, DEVICE)::type_id::create("logic_vector_seq", this);
            logic_vector_seq.tr_plan = tr_plan;
            logic_vector_seq.randomize();

            byte_array_seq         = byte_array_sequence#(PCIE_UPHDR_WIDTH, PCIE_DOWNHDR_WIDTH, RQ_TUSER_WIDTH, RCB_SIZE, CLK_PERIOD, DEVICE)::type_id::create("byte_array_seq", this);
            byte_array_seq.tr_plan = tr_plan;
            byte_array_seq.randomize();
            if (DEVICE == "STRATIX10" || DEVICE == "AGILEX") begin
                fork
                    logic_vector_seq.start(m_env_rc_mfb.m_sequencer.m_meta);
                    byte_array_seq.start(m_env_rc_mfb.m_sequencer.m_data);
                join_any
            end else begin
                fork
                    byte_array_seq.start(m_env_rc_axi.m_sequencer.m_data);
                join_any
            end

        end
    endtask
endclass

