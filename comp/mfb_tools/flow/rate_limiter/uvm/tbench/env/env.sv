// env.sv: Verification environment
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Tomas Hak <xhakto01@vut.cz>

// SPDX-License-Identifier: BSD-3-Clause

class env#(MI_DATA_WIDTH, MI_ADDR_WIDTH, MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH, INTERVAL_COUNT, SHAPING_TYPE, CLK_PERIOD) extends uvm_env;
    `uvm_component_param_utils(uvm_rate_limiter::env#(MI_DATA_WIDTH, MI_ADDR_WIDTH, MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH, INTERVAL_COUNT, SHAPING_TYPE, CLK_PERIOD));

    uvm_reset::agent                                                                                                   m_reset;
    uvm_mi::regmodel                   #(regmodel#(INTERVAL_COUNT), MI_DATA_WIDTH, MI_ADDR_WIDTH)                      m_regmodel;
    uvm_logic_vector_array_mfb::env_rx #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH) m_env_rx;
    uvm_logic_vector_array_mfb::env_tx #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH) m_env_tx;
    uvm_rate_limiter::virt_sequencer   #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH) m_sequencer;
    scoreboard                         #(MFB_ITEM_WIDTH, MFB_META_WIDTH, INTERVAL_COUNT, SHAPING_TYPE, CLK_PERIOD)     sc;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        uvm_reset::config_item                    m_config_reset;
        uvm_mi::regmodel_config                   m_mi_config;
        uvm_logic_vector_array_mfb::config_item   m_config_rx;
        uvm_logic_vector_array_mfb::config_item   m_config_tx;

        m_config_reset                   = new();
        m_config_reset.active            = UVM_ACTIVE;
        m_config_reset.interface_name    = "vif_reset";
        uvm_config_db#(uvm_reset::config_item)::set(this, "m_reset", "m_config", m_config_reset);
        m_reset = uvm_reset::agent::type_id::create("m_reset", this);

        m_mi_config                      = new();
        m_mi_config.addr_base            = 'h0;
        m_mi_config.agent.active         = UVM_ACTIVE;
        m_mi_config.agent.interface_name = "vif_mi";
        uvm_config_db#(uvm_mi::regmodel_config)::set(this, "m_regmodel", "m_config", m_mi_config);
        m_regmodel = uvm_mi::regmodel#(regmodel#(INTERVAL_COUNT), MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::create("m_regmodel", this);

        m_config_rx                      = new();
        m_config_rx.active               = UVM_ACTIVE;
        m_config_rx.interface_name       = "vif_rx";
        m_config_rx.meta_behav           = uvm_logic_vector_array_mfb::config_item::META_SOF;
        uvm_config_db#(uvm_logic_vector_array_mfb::config_item)::set(this, "m_env_rx", "m_config", m_config_rx);
        m_env_rx = uvm_logic_vector_array_mfb::env_rx#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH)::type_id::create("m_env_rx", this);

        m_config_tx                      = new();
        m_config_tx.active               = UVM_ACTIVE;
        m_config_tx.interface_name       = "vif_tx";
        m_config_tx.meta_behav           = uvm_logic_vector_array_mfb::config_item::META_SOF;
        uvm_config_db#(uvm_logic_vector_array_mfb::config_item)::set(this, "m_env_tx", "m_config", m_config_tx);
        m_env_tx = uvm_logic_vector_array_mfb::env_tx#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH)::type_id::create("m_env_tx", this);

        m_sequencer = uvm_rate_limiter::virt_sequencer#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH)::type_id::create("m_sequencer", this);

        sc = scoreboard#(MFB_ITEM_WIDTH, MFB_META_WIDTH, INTERVAL_COUNT, SHAPING_TYPE, CLK_PERIOD)::type_id::create("sc", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        m_env_rx.analysis_port_data.connect(sc.analysis_export_rx_packet);
        m_env_rx.analysis_port_meta.connect(sc.analysis_export_rx_meta);
        m_env_tx.analysis_port_data.connect(sc.analysis_export_tx_packet);
        m_env_tx.analysis_port_meta.connect(sc.analysis_export_tx_meta);

        m_reset.sync_connect(m_env_rx.reset_sync);
        m_reset.sync_connect(m_env_tx.reset_sync);

        m_sequencer.m_reset       = m_reset.m_sequencer;
        m_sequencer.m_mfb_tx      = m_env_tx.m_sequencer;
        m_sequencer.m_mfb_rx_data = m_env_rx.m_sequencer.m_data;
        m_sequencer.m_mfb_rx_meta = m_env_rx.m_sequencer.m_meta;

        sc.regmodel_set(m_regmodel.m_regmodel);
    endfunction
endclass
