//-- env.sv: Verification environment
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author:   David Beneš <xbenes52@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// Environment for functional verification of encode.

class env #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) extends uvm_env;

    `uvm_component_param_utils(uvm_mfb_pipe::env #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH));

    uvm_logic_vector_array_mfb::env_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) mfb_rx_env;
    uvm_logic_vector_array_mfb::env_tx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) mfb_tx_env;

    uvm_reset::agent        m_reset;
    uvm_reset::config_item  m_config_reset;

    uvm_mfb_pipe::virt_sequencer#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) vscr;

    scoreboard #(ITEM_WIDTH, META_WIDTH) m_scoreboard;

    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);
        uvm_logic_vector_array_mfb::config_item mfb_rx_cfg;
        uvm_logic_vector_array_mfb::config_item mfb_tx_cfg;

        mfb_rx_cfg = new;
        mfb_tx_cfg = new;

        mfb_rx_cfg.active = UVM_ACTIVE;
        mfb_tx_cfg.active = UVM_ACTIVE;

        mfb_rx_cfg.interface_name = "vif_rx";
        mfb_tx_cfg.interface_name = "vif_tx";

        mfb_rx_cfg.meta_behav = uvm_logic_vector_array_mfb::config_item::META_SOF;
        mfb_tx_cfg.meta_behav = uvm_logic_vector_array_mfb::config_item::META_SOF;

        m_config_reset                = new;
        m_config_reset.active         = UVM_ACTIVE;
        m_config_reset.interface_name = "vif_reset";

        uvm_config_db #(uvm_reset::config_item)::set(this, "m_reset", "m_config", m_config_reset);
        m_reset = uvm_reset::agent::type_id::create("m_reset", this);

        uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, "mfb_rx_env", "m_config", mfb_rx_cfg);
        uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, "mfb_tx_env", "m_config", mfb_tx_cfg);

        mfb_rx_env = uvm_logic_vector_array_mfb::env_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::type_id::create("mfb_rx_env", this);
        mfb_tx_env = uvm_logic_vector_array_mfb::env_tx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::type_id::create("mfb_tx_env", this);

        m_scoreboard  = scoreboard #(ITEM_WIDTH, META_WIDTH)::type_id::create("m_scoreboard", this);
        vscr   = uvm_mfb_pipe::virt_sequencer#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::type_id::create("vscr",this);
    endfunction

     // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);
        //Connect RX environment
        mfb_rx_env.analysis_port_data.connect(m_scoreboard.analysis_imp_mfb_rx_data);
        mfb_rx_env.analysis_port_meta.connect(m_scoreboard.analysis_imp_mfb_rx_meta);

        //Connect TX enviornment
        mfb_tx_env.analysis_port_data.connect(m_scoreboard.data_cmp.analysis_imp_dut);
        mfb_tx_env.analysis_port_meta.connect(m_scoreboard.meta_cmp.analysis_imp_dut);

        m_reset.sync_connect(mfb_rx_env.reset_sync);
        m_reset.sync_connect(mfb_tx_env.reset_sync);

        vscr.m_reset        = m_reset.m_sequencer;
        vscr.m_mfb_data_sqr = mfb_rx_env.m_sequencer.m_data;
        vscr.m_mfb_meta_sqr = mfb_rx_env.m_sequencer.m_meta;

    endfunction
endclass
