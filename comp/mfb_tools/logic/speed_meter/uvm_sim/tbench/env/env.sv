//-- env.sv: Verification environment
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// Environment for functional verification of encode.
// This environment containts two mii agents.
class env #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, MI_DATA_WIDTH, MI_ADDRESS_WIDTH, SPACE_SIZE_MIN_RX, SPACE_SIZE_MAX_RX, SPACE_SIZE_MIN_TX, SPACE_SIZE_MAX_TX) extends uvm_env;

    `uvm_component_param_utils(uvm_speed_meter::env #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, MI_DATA_WIDTH, MI_ADDRESS_WIDTH, SPACE_SIZE_MIN_RX, SPACE_SIZE_MAX_RX, SPACE_SIZE_MIN_TX, SPACE_SIZE_MAX_TX));

    uvm_logic_vector_array_mfb::env_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0) m_mfb_rx_env;
    uvm_logic_vector_array_mfb::env_tx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0) m_mfb_tx_env;
    uvm_logic_vector_array_mfb::config_item                                               m_mfb_rx_config;
    uvm_logic_vector_array_mfb::config_item                                               m_mfb_tx_config;

    uvm_speed_meter::virt_sequencer#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, MI_DATA_WIDTH, MI_ADDRESS_WIDTH) vscr;

    uvm_reset::agent       m_reset;
    uvm_reset::config_item m_reset_config;

    uvm_mi::agent_slave #(MI_DATA_WIDTH, MI_ADDRESS_WIDTH) m_mi_agent;
    uvm_mi::config_item                                    m_mi_config;


    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);

        m_mfb_rx_config                = new;
        m_mfb_rx_config.active         = UVM_ACTIVE;
        m_mfb_rx_config.interface_name = "vif_rx";
        m_mfb_rx_config.meta_behav     = uvm_logic_vector_array_mfb::config_item::META_NONE;
        m_mfb_rx_config.seq_cfg        = new();
        m_mfb_rx_config.seq_cfg.space_size_set(SPACE_SIZE_MIN_RX, SPACE_SIZE_MAX_RX);

        m_mfb_tx_config                = new;
        m_mfb_tx_config.active         = UVM_ACTIVE;
        m_mfb_tx_config.interface_name = "vif_tx";
        m_mfb_tx_config.meta_behav     = uvm_logic_vector_array_mfb::config_item::META_NONE;
        m_mfb_tx_config.seq_cfg        = new();
        m_mfb_tx_config.seq_cfg.space_size_set(SPACE_SIZE_MIN_TX, SPACE_SIZE_MAX_TX);

        m_reset_config                = new;
        m_reset_config.active         = UVM_ACTIVE;
        m_reset_config.interface_name = "vif_reset";

        m_mi_config                = new();
        m_mi_config.active         = UVM_ACTIVE;
        m_mi_config.interface_name = "vif_mi";
        uvm_config_db#(uvm_mi::config_item)::set(this, "m_mi_agent", "m_config", m_mi_config);
        m_mi_agent = uvm_mi::agent_slave #(MI_DATA_WIDTH, MI_ADDRESS_WIDTH)::type_id::create("m_mi_agent", this);

        uvm_config_db#(uvm_reset::config_item)::set(this, "m_reset", "m_config", m_reset_config);
        m_reset = uvm_reset::agent::type_id::create("m_reset", this);

        uvm_config_db#(uvm_logic_vector_array_mfb::config_item)::set(this, "m_mfb_rx_env", "m_config", m_mfb_rx_config);
        uvm_config_db#(uvm_logic_vector_array_mfb::config_item)::set(this, "m_mfb_tx_env", "m_config", m_mfb_tx_config);

        m_mfb_rx_env = uvm_logic_vector_array_mfb::env_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0)::type_id::create("m_mfb_rx_env", this);
        m_mfb_tx_env = uvm_logic_vector_array_mfb::env_tx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0)::type_id::create("m_mfb_tx_env", this);

        vscr   = uvm_speed_meter::virt_sequencer#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, MI_DATA_WIDTH, MI_ADDRESS_WIDTH)::type_id::create("vscr",this);
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);

        vscr.m_mi_sqr       = m_mi_agent.m_sequencer;
        vscr.m_reset_sqr    = m_reset.m_sequencer;
        vscr.m_mfb_data_sqr = m_mfb_rx_env.m_sequencer.m_data;
        vscr.m_mfb_rdy_sqr  = m_mfb_tx_env.m_sequencer;
        m_reset.sync_connect(m_mfb_rx_env.reset_sync);

    endfunction
endclass
