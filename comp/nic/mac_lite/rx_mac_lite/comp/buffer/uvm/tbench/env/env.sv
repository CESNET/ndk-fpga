// env.sv: Verification environment
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

// Environment for the functional verification.
class env #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH, DUT_PATH) extends uvm_env;
    `uvm_component_param_utils(uvm_rx_mac_lite_buffer::env #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH, DUT_PATH));

    uvm_logic_vector_array_mfb::env_rx #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH) m_env_rx;
    uvm_logic_vector_array_mfb::env_tx #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0)              m_env_tx_mfb;
    uvm_logic_vector_mvb::env_tx       #(MFB_REGIONS, MFB_META_WIDTH)                                                  m_env_tx_mvb;


    uvm_rx_mac_lite_buffer::virt_sequencer #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH) vscr;

    uvm_reset::agent                               m_reset_rx;
    uvm_reset::agent                               m_reset_tx;
    uvm_logic_vector_array::agent#(MFB_ITEM_WIDTH) m_logic_vector_array_agent;

    scoreboard #(MFB_ITEM_WIDTH, MFB_META_WIDTH, MFB_REGIONS, DUT_PATH) sc;

    // Constructor of the environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Create base components of the environment.
    function void build_phase(uvm_phase phase);

        uvm_reset::config_item                  m_config_reset_rx;
        uvm_reset::config_item                  m_config_reset_tx;
        uvm_logic_vector_array_mfb::config_item m_config_rx;
        uvm_logic_vector_array_mfb::config_item m_config_tx;
        uvm_logic_vector_mvb::config_item       m_config_mvb_tx;
        uvm_logic_vector_array::config_item     m_logic_vector_array_agent_cfg;

        m_logic_vector_array_agent_cfg        = new();
        m_logic_vector_array_agent_cfg.active = UVM_ACTIVE;
        uvm_config_db #(uvm_logic_vector_array::config_item)::set(this, "m_logic_vector_array_agent", "m_config", m_logic_vector_array_agent_cfg);
        m_logic_vector_array_agent   = uvm_logic_vector_array::agent#(MFB_ITEM_WIDTH)::type_id::create("m_logic_vector_array_agent", this);

        m_config_reset_rx                = new;
        m_config_reset_rx.active         = UVM_ACTIVE;
        m_config_reset_rx.interface_name = "vif_reset_rx";

        uvm_config_db #(uvm_reset::config_item)::set(this, "m_reset_rx", "m_config", m_config_reset_rx);
        m_reset_rx = uvm_reset::agent::type_id::create("m_reset_rx", this);

        m_config_reset_tx                = new;
        m_config_reset_tx.active         = UVM_ACTIVE;
        m_config_reset_tx.interface_name = "vif_reset_tx";

        uvm_config_db #(uvm_reset::config_item)::set(this, "m_reset_tx", "m_config", m_config_reset_tx);
        m_reset_tx = uvm_reset::agent::type_id::create("m_reset_tx", this);


        // Passing the virtual interfaces
        m_config_rx                = new;
        m_config_rx.active         = UVM_ACTIVE;
        m_config_rx.interface_name = "vif_rx";
        m_config_rx.meta_behav     = uvm_logic_vector_array_mfb::config_item::META_EOF;

        uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, "m_env_rx", "m_config", m_config_rx);
        m_env_rx = uvm_logic_vector_array_mfb::env_rx#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH)::type_id::create("m_env_rx", this);

        m_config_tx                = new;
        m_config_tx.active         = UVM_ACTIVE;
        m_config_tx.interface_name = "vif_tx";
        m_config_tx.meta_behav     = uvm_logic_vector_array_mfb::config_item::META_NONE;

        uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, "m_env_tx_mfb", "m_config", m_config_tx);
        m_env_tx_mfb = uvm_logic_vector_array_mfb::env_tx#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0)::type_id::create("m_env_tx_mfb", this);

        m_config_mvb_tx                = new;
        m_config_mvb_tx.active         = UVM_ACTIVE;
        m_config_mvb_tx.interface_name = "vif_mvb_tx";

        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "m_env_tx_mvb", "m_config", m_config_mvb_tx);
        m_env_tx_mvb = uvm_logic_vector_mvb::env_tx#(MFB_REGIONS, MFB_META_WIDTH)::type_id::create("m_env_tx_mvb", this);

        sc   = scoreboard#(MFB_ITEM_WIDTH, MFB_META_WIDTH, MFB_REGIONS, DUT_PATH)::type_id::create("sc", this);
        vscr = uvm_rx_mac_lite_buffer::virt_sequencer#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH)::type_id::create("vscr",this);

    endfunction

    // Connect agent's ports with ports from the scoreboard.
    function void connect_phase(uvm_phase phase);

        m_env_rx.analysis_port_data.connect(sc.analysis_imp_mfb_data);
        m_env_rx.analysis_port_meta.connect(sc.analysis_imp_mfb_meta);

        m_env_tx_mfb.analysis_port_data.connect(sc.out_mfb_data);
        m_env_tx_mvb.analysis_port.connect(sc.out_mvb_data);

        m_reset_rx.sync_connect(m_env_rx.reset_sync);
        m_reset_tx.sync_connect(m_env_tx_mfb.reset_sync);
        m_reset_tx.sync_connect(m_env_tx_mvb.reset_sync);

        vscr.m_reset_rx_sqr = m_reset_rx.m_sequencer;
        vscr.m_reset_tx_sqr = m_reset_tx.m_sequencer;
        vscr.m_mfb_rdy_sqr  = m_env_tx_mfb.m_sequencer;
        vscr.m_mvb_rdy_sqr  = m_env_tx_mvb.m_sequencer;
        vscr.m_mfb_data_sqr = m_env_rx.m_sequencer.m_data;
        vscr.m_mfb_meta_sqr = m_env_rx.m_sequencer.m_meta;

    endfunction

endclass
