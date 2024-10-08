//-- env.sv: Verification environment
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// Environment for functional verification of encode.
// This environment containts two mii agents.
class env #(ITEMS, LUT_WIDTH, REG_DEPTH, SW_WIDTH, SLICE_WIDTH, LUT_DEPTH, SPACE_SIZE_MIN, SPACE_SIZE_MAX) extends uvm_env;

    `uvm_component_param_utils(uvm_lookup_table::env #(ITEMS, LUT_WIDTH, REG_DEPTH, SW_WIDTH, SLICE_WIDTH, LUT_DEPTH, SPACE_SIZE_MIN, SPACE_SIZE_MAX));

    uvm_logic_vector_mvb::env_rx #(ITEMS, REG_DEPTH-SLICE_WIDTH) m_mvb_rx_env;
    uvm_logic_vector_mvb::config_item                            m_mvb_rx_config;

    uvm_logic_vector_mvb::env_tx #(ITEMS, LUT_WIDTH) m_mvb_tx_env;
    uvm_logic_vector_mvb::config_item                m_mvb_tx_config;

    uvm_lookup_table::virt_sequencer#(ITEMS, LUT_WIDTH, REG_DEPTH, SLICE_WIDTH, SW_WIDTH) vscr;

    uvm_reset::agent         m_reset;
    uvm_reset::config_item   m_reset_config;

    uvm_mi::agent_slave #(SW_WIDTH, REG_DEPTH) m_mi_agent;
    uvm_mi::config_item                        m_mi_config;

    uvm_mvb::coverage #(ITEMS, REG_DEPTH-SLICE_WIDTH) m_mvb_rx_cover;
    uvm_mvb::coverage #(ITEMS, LUT_WIDTH)             m_mvb_tx_cover;

    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);

        m_mvb_rx_cover  = new("m_mvb_rx_cover");
        m_mvb_tx_cover  = new("m_mvb_tx_cover");
        m_mvb_tx_config = new;
        m_mvb_rx_config = new;

        m_mvb_tx_config.active = UVM_ACTIVE;
        m_mvb_rx_config.active = UVM_ACTIVE;

        m_mvb_tx_config.interface_name = "vif_tx";
        m_mvb_rx_config.interface_name = "vif_rx";

        m_mvb_rx_config.seq_cfg = new();
        m_mvb_rx_config.seq_cfg.space_size_set(SPACE_SIZE_MIN, SPACE_SIZE_MAX);

        m_reset_config                = new;
        m_reset_config.active         = UVM_ACTIVE;
        m_reset_config.interface_name = "vif_reset";

        m_mi_config                = new();
        m_mi_config.active         = UVM_ACTIVE;
        m_mi_config.interface_name = "vif_mi";
        uvm_config_db#(uvm_mi::config_item)::set(this, "m_mi_agent", "m_config", m_mi_config);
        m_mi_agent = uvm_mi::agent_slave #(SW_WIDTH, REG_DEPTH)::type_id::create("m_mi_agent", this);

        uvm_config_db#(uvm_reset::config_item)::set(this, "m_reset", "m_config", m_reset_config);
        m_reset = uvm_reset::agent::type_id::create("m_reset", this);

        uvm_config_db#(uvm_logic_vector_mvb::config_item)::set(this, "m_mvb_tx_env", "m_config", m_mvb_tx_config);
        uvm_config_db#(uvm_logic_vector_mvb::config_item)::set(this, "m_mvb_rx_env", "m_config", m_mvb_rx_config);

        m_mvb_tx_env = uvm_logic_vector_mvb::env_tx #(ITEMS, LUT_WIDTH)::type_id::create("m_mvb_tx_env", this);
        m_mvb_rx_env = uvm_logic_vector_mvb::env_rx #(ITEMS, REG_DEPTH-SLICE_WIDTH)::type_id::create("m_mvb_rx_env", this);

        vscr   = uvm_lookup_table::virt_sequencer#(ITEMS, LUT_WIDTH, REG_DEPTH, SLICE_WIDTH, SW_WIDTH)::type_id::create("vscr",this);
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);

        m_reset.sync_connect(m_mvb_rx_env.reset_sync);
        m_reset.sync_connect(m_mvb_tx_env.reset_sync);
        vscr.m_mi_sqr = m_mi_agent.m_sequencer;

        m_mvb_rx_env.m_mvb_agent.analysis_port.connect(m_mvb_rx_cover.analysis_export);
        m_mvb_tx_env.m_mvb_agent.analysis_port.connect(m_mvb_tx_cover.analysis_export);

        vscr.m_reset_sqr    = m_reset.m_sequencer;
        vscr.m_mvb_data_sqr = m_mvb_rx_env.m_sequencer;
        vscr.m_mvb_rdy_sqr  = m_mvb_tx_env.m_sequencer;

    endfunction
endclass
