// env.sv: Verification environment
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kříž <danielkriz@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

// Environment for the functional verification.
class env #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, RX_MFB_META_WIDTH, TX_MFB_META_WIDTH, TIMESTAMP_WIDTH, QUEUES, TIMESTAMP_FORMAT, MI_DATA_WIDTH, MI_ADDR_WIDTH) extends uvm_env;
    `uvm_component_param_utils(uvm_timestamp_limiter::env #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, RX_MFB_META_WIDTH, TX_MFB_META_WIDTH, TIMESTAMP_WIDTH, QUEUES, TIMESTAMP_FORMAT, MI_DATA_WIDTH, MI_ADDR_WIDTH));

    uvm_logic_vector_array_mfb::env_rx #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, RX_MFB_META_WIDTH) m_env_rx;
    uvm_logic_vector_array_mfb::env_tx #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, TX_MFB_META_WIDTH) m_env_tx;

    uvm_timestamp_limiter::virt_sequencer #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, RX_MFB_META_WIDTH, TX_MFB_META_WIDTH, QUEUES) vscr;

    uvm_reset::agent                               m_reset;
    uvm_logic_vector_array::agent#(MFB_ITEM_WIDTH) m_logic_vector_array_agent;

    uvm_mi::regmodel#(uvm_timestamp_limiter::regmodel#(QUEUES), MI_DATA_WIDTH, MI_ADDR_WIDTH) m_regmodel;

    scoreboard #(MFB_ITEM_WIDTH, RX_MFB_META_WIDTH, TX_MFB_META_WIDTH, TIMESTAMP_WIDTH, QUEUES, TIMESTAMP_FORMAT) sc;

    // Constructor of the environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Create base components of the environment.
    function void build_phase(uvm_phase phase);

        uvm_reset::config_item                  m_config_reset;
        uvm_logic_vector_array_mfb::config_item m_config_rx;
        uvm_logic_vector_array_mfb::config_item m_config_tx;
        uvm_logic_vector_array::config_item     m_logic_vector_array_agent_cfg;
        uvm_mi::regmodel_config                 m_mi_config;

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
        m_config_rx                = new;
        m_config_rx.active         = UVM_ACTIVE;
        m_config_rx.interface_name = "vif_rx";
        m_config_rx.meta_behav     = uvm_logic_vector_array_mfb::config_item::META_SOF;

        uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, "m_env_rx", "m_config", m_config_rx);
        m_env_rx = uvm_logic_vector_array_mfb::env_rx#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, RX_MFB_META_WIDTH)::type_id::create("m_env_rx", this);

        m_config_tx                = new;
        m_config_tx.active         = UVM_ACTIVE;
        m_config_tx.interface_name = "vif_tx";
        m_config_tx.meta_behav     = (TX_MFB_META_WIDTH > 0) ? uvm_logic_vector_array_mfb::config_item::META_SOF : uvm_logic_vector_array_mfb::config_item::META_NONE;

        uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, "m_env_tx", "m_config", m_config_tx);
        m_env_tx = uvm_logic_vector_array_mfb::env_tx#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, TX_MFB_META_WIDTH)::type_id::create("m_env_tx", this);

        m_mi_config                      = new();
        m_mi_config.addr_base            = 'h0;
        m_mi_config.agent.active         = UVM_ACTIVE;
        m_mi_config.agent.interface_name = "vif_mi";
        uvm_config_db#(uvm_mi::regmodel_config)::set(this, "m_regmodel", "m_config", m_mi_config);
        m_regmodel = uvm_mi::regmodel#(uvm_timestamp_limiter::regmodel#(QUEUES), MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::create("m_regmodel", this);

        sc   = scoreboard#(MFB_ITEM_WIDTH, RX_MFB_META_WIDTH, TX_MFB_META_WIDTH, TIMESTAMP_WIDTH, QUEUES, TIMESTAMP_FORMAT)::type_id::create("sc", this);
        vscr = uvm_timestamp_limiter::virt_sequencer#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, RX_MFB_META_WIDTH, TX_MFB_META_WIDTH, QUEUES)::type_id::create("vscr",this);

    endfunction

    // Connect agent's ports with ports from the scoreboard.
    function void connect_phase(uvm_phase phase);

        m_env_rx.analysis_port_data.connect(sc.analysis_imp_mfb_data);
        m_env_rx.analysis_port_meta.connect(sc.analysis_imp_mfb_meta);

        m_env_tx.analysis_port_data.connect(sc.out_data);
        m_env_tx.analysis_port_meta.connect(sc.out_meta);

        m_reset.sync_connect(m_env_rx.reset_sync);
        m_reset.sync_connect(m_env_tx.reset_sync);

        vscr.m_reset_sqr       = m_reset.m_sequencer;
        vscr.m_mfb_rdy_sqr     = m_env_tx.m_sequencer;
        vscr.m_mfb_data_sqr    = m_env_rx.m_sequencer.m_data;
        vscr.m_mfb_meta_sqr    = m_env_rx.m_sequencer.m_meta;
        vscr.m_regmodel        = m_regmodel.m_regmodel;

    endfunction

endclass
