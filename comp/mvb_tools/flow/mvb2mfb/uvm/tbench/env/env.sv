// env.sv: Verification environment
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

// Environment for the functional verification.
class env #(MFB_REGIONS, MVB_ITEMS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH, MVB_ITEM_WIDTH) extends uvm_env;
    `uvm_component_param_utils(uvm_mvb2mfb::env #(MFB_REGIONS, MVB_ITEMS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH, MVB_ITEM_WIDTH));

    uvm_logic_vector_array_mfb::env_tx #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH) m_env_tx;
    uvm_logic_vector_mvb::env_rx       #(MVB_ITEMS, MVB_ITEM_WIDTH)                                                                     m_env_rx_mvb;


    uvm_mvb2mfb::virt_sequencer #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH, MVB_ITEM_WIDTH) vscr;

    uvm_reset::agent                               m_reset;
    uvm_logic_vector_array::agent#(MFB_ITEM_WIDTH) m_logic_vector_array_agent;

    scoreboard #(MFB_ITEM_WIDTH, MVB_ITEM_WIDTH, MFB_META_WIDTH) sc;

    // Constructor of the environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Create base components of the environment.
    function void build_phase(uvm_phase phase);

        uvm_reset::config_item                  m_config_reset;
        uvm_logic_vector_array_mfb::config_item m_config_rx;
        uvm_logic_vector_array_mfb::config_item m_config_tx;
        uvm_logic_vector_mvb::config_item       m_config_mvb_rx;
        uvm_logic_vector_array::config_item     m_logic_vector_array_agent_cfg;

        m_logic_vector_array_agent_cfg        = new();
        m_logic_vector_array_agent_cfg.active = UVM_ACTIVE;
        uvm_config_db #(uvm_logic_vector_array::config_item)::set(this, "m_logic_vector_array_agent", "m_config", m_logic_vector_array_agent_cfg);
        m_logic_vector_array_agent   = uvm_logic_vector_array::agent#(MFB_ITEM_WIDTH)::type_id::create("m_logic_vector_array_agent", this);

        m_config_reset                = new;
        m_config_reset.active         = UVM_ACTIVE;
        m_config_reset.interface_name = "vif_reset";

        uvm_config_db #(uvm_reset::config_item)::set(this, "m_reset", "m_config", m_config_reset);
        m_reset = uvm_reset::agent::type_id::create("m_reset", this);

        // Passing the virtual interfaces

        m_config_tx                = new;
        m_config_tx.active         = UVM_ACTIVE;
        m_config_tx.interface_name = "vif_tx";
        m_config_tx.meta_behav     = uvm_logic_vector_array_mfb::config_item::META_SOF;


        uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, "m_env_tx", "m_config", m_config_tx);
        m_env_tx = uvm_logic_vector_array_mfb::env_tx#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH)::type_id::create("m_env_tx", this);

        m_config_mvb_rx                = new;
        m_config_mvb_rx.active         = UVM_ACTIVE;
        m_config_mvb_rx.interface_name = "vif_mvb_rx";

        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "m_env_rx_mvb", "m_config", m_config_mvb_rx);
        m_env_rx_mvb = uvm_logic_vector_mvb::env_rx#(MVB_ITEMS, MVB_ITEM_WIDTH)::type_id::create("m_env_rx_mvb", this);

        sc   = scoreboard#(MFB_ITEM_WIDTH, MVB_ITEM_WIDTH, MFB_META_WIDTH)::type_id::create("sc", this);
        vscr = uvm_mvb2mfb::virt_sequencer#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH, MVB_ITEM_WIDTH)::type_id::create("vscr",this);

    endfunction

    // Connect agent's ports with ports from the scoreboard.
    function void connect_phase(uvm_phase phase);

        m_env_rx_mvb.analysis_port.connect(sc.analysis_imp_mvb_data);
        m_env_tx.analysis_port_data.connect(sc.out_data);
        m_env_tx.analysis_port_meta.connect(sc.out_meta);

        m_reset.sync_connect(m_env_tx.reset_sync);
        m_reset.sync_connect(m_env_rx_mvb.reset_sync);

        vscr.m_reset_sqr    = m_reset.m_sequencer;
        vscr.m_mfb_rdy_sqr  = m_env_tx.m_sequencer;
        vscr.m_mvb_data_sqr = m_env_rx_mvb.m_sequencer;

    endfunction

endclass
