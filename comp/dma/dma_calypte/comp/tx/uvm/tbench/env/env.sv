// env.sv: Main verification environment
// Copyright (C) 2022-2024 CESNET z. s. p. o.
// Author(s): Daniel Kriz <danielkriz@cesnet.cz>
//            Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class env #(
    string       DEVICE,
    int unsigned MI_WIDTH,

    int unsigned USR_MFB_REGIONS,
    int unsigned USR_MFB_REGION_SIZE,
    int unsigned USR_MFB_BLOCK_SIZE,
    int unsigned USR_MFB_ITEM_WIDTH,

    int unsigned PCIE_CQ_MFB_REGIONS,
    int unsigned PCIE_CQ_MFB_REGION_SIZE,
    int unsigned PCIE_CQ_MFB_BLOCK_SIZE,
    int unsigned PCIE_CQ_MFB_ITEM_WIDTH,

    int unsigned CHANNELS,
    int unsigned HDR_META_WIDTH,
    int unsigned DATA_POINTER_WIDTH,
    int unsigned PKT_SIZE_MAX,
    int unsigned PCIE_LEN_MAX,
    int unsigned UPD_THRESHOLD
) extends uvm_env;

    `uvm_component_param_utils(uvm_tx_dma_calypte::env #(
        DEVICE,
        MI_WIDTH,

        USR_MFB_REGIONS,
        USR_MFB_REGION_SIZE,
        USR_MFB_BLOCK_SIZE,
        USR_MFB_ITEM_WIDTH,

        PCIE_CQ_MFB_REGIONS,
        PCIE_CQ_MFB_REGION_SIZE,
        PCIE_CQ_MFB_BLOCK_SIZE,
        PCIE_CQ_MFB_ITEM_WIDTH,

        CHANNELS,
        HDR_META_WIDTH,
        DATA_POINTER_WIDTH,
        PKT_SIZE_MAX,
        PCIE_LEN_MAX,
        UPD_THRESHOLD
    ))

    localparam USR_MFB_META_WIDTH      = HDR_META_WIDTH + $clog2(PKT_SIZE_MAX+1) + $clog2(CHANNELS);
    localparam UPD_STOP_REQ_MVB_ITEM_W = (DATA_POINTER_WIDTH-3) + DATA_POINTER_WIDTH + 1 + 64;
    localparam RT_UPD_MVB_ITEM_W       = (DATA_POINTER_WIDTH-3) + DATA_POINTER_WIDTH + $clog2(CHANNELS);

    sequencer #(USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE, USR_MFB_ITEM_WIDTH, CHANNELS, HDR_META_WIDTH,
                PKT_SIZE_MAX, DATA_POINTER_WIDTH, PCIE_CQ_MFB_REGIONS, PCIE_CQ_MFB_REGION_SIZE, PCIE_CQ_MFB_BLOCK_SIZE,
                PCIE_CQ_MFB_ITEM_WIDTH)                                                        m_sequencer;
    uvm_reset::agent                                                                           m_reset_agent;

    // ----------------------------------------------------------
    // TX DMA interfaces
    // ----------------------------------------------------------
    uvm_tx_dma_calypte_cq::env #(DEVICE, PCIE_CQ_MFB_REGIONS, PCIE_CQ_MFB_REGION_SIZE, PCIE_CQ_MFB_BLOCK_SIZE,
                                 PCIE_CQ_MFB_ITEM_WIDTH, CHANNELS, DATA_POINTER_WIDTH, PCIE_LEN_MAX) m_cq_mfb_env;
    uvm_logic_vector_array_mfb::env_tx #(USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE, USR_MFB_ITEM_WIDTH,
                                         USR_MFB_META_WIDTH)                                   m_tx_mfb_env;
    uvm_logic_vector_mvb::env_tx #(PCIE_CQ_MFB_REGIONS, 1)                                     m_pkt_drop_meta_mvb_env;

    // ----------------------------------------------------------
    // Pointer update interfaces
    // ----------------------------------------------------------
    uvm_logic_vector_array_mfb::env_tx #(PCIE_CQ_MFB_REGIONS, PCIE_CQ_MFB_REGION_SIZE,
                                         PCIE_CQ_MFB_BLOCK_SIZE, PCIE_CQ_MFB_ITEM_WIDTH,
                                         sv_pcie_meta_pack::PCIE_RQ_META_WIDTH)                m_ptr_upd_mfb_env;
    uvm_logic_vector_mvb::env_tx #(1, UPD_STOP_REQ_MVB_ITEM_W)                                 m_upd_stop_req_mvb_env;
    uvm_logic_vector_mvb::env_tx #(1, $clog2(CHANNELS))                                        m_chan_start_req_mvb_env;
    uvm_logic_vector_mvb::env_tx #(1, RT_UPD_MVB_ITEM_W)                                       m_rt_upd_mvb_env;

    uvm_mi::regmodel #(uvm_tx_dma_calypte_regs::regmodel_top #(CHANNELS, DATA_POINTER_WIDTH), MI_WIDTH,
                       MI_WIDTH)                                                               m_regmodel_top;
    coverage #(PCIE_CQ_MFB_REGIONS, PCIE_CQ_MFB_REGION_SIZE, PCIE_CQ_MFB_BLOCK_SIZE, PCIE_CQ_MFB_ITEM_WIDTH,
               sv_pcie_meta_pack::PCIE_CQ_META_WIDTH)                                          m_coverage;
    scoreboard #(USR_MFB_ITEM_WIDTH, PCIE_CQ_MFB_ITEM_WIDTH, CHANNELS, DATA_POINTER_WIDTH, USR_MFB_META_WIDTH,
                 DEVICE, UPD_THRESHOLD)                                                        m_scoreboard;

    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
        m_coverage = new("m_coverage");
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);
        uvm_reset::config_item                  m_reset_cfg;
        uvm_tx_dma_calypte_cq::config_item      m_cq_mfb_env_cfg;
        uvm_logic_vector_array_mfb::config_item m_tx_mfb_env_cfg;
        uvm_logic_vector_mvb::config_item       m_pkt_drop_meta_mvb_env_cfg;
        uvm_logic_vector_array_mfb::config_item m_ptr_upd_mfb_env_cfg;
        uvm_logic_vector_mvb::config_item       m_upd_stop_req_mvb_env_cfg;
        uvm_logic_vector_mvb::config_item       m_chan_start_req_mvb_env_cfg;
        uvm_logic_vector_mvb::config_item       m_rt_upd_mvb_env_cfg;
        uvm_mi::regmodel_config                 m_mi_config;

        m_reset_cfg                = new;
        m_reset_cfg.active         = UVM_ACTIVE;
        m_reset_cfg.interface_name = "reset_vif";
        uvm_config_db #(uvm_reset::config_item)::set(this, "m_reset_agent", "m_config", m_reset_cfg);
        m_reset_agent = uvm_reset::agent::type_id::create("m_reset_agent", this);

        m_cq_mfb_env_cfg                = new;
        m_cq_mfb_env_cfg.active         = UVM_ACTIVE;
        m_cq_mfb_env_cfg.interface_name = "cq_mfb_vif";
        uvm_config_db #(uvm_tx_dma_calypte_cq::config_item)::set(this, "m_cq_mfb_env", "m_config", m_cq_mfb_env_cfg);
        m_cq_mfb_env = uvm_tx_dma_calypte_cq::env #(DEVICE, PCIE_CQ_MFB_REGIONS, PCIE_CQ_MFB_REGION_SIZE,
                                                    PCIE_CQ_MFB_BLOCK_SIZE, PCIE_CQ_MFB_ITEM_WIDTH, CHANNELS,
                                                    DATA_POINTER_WIDTH, PCIE_LEN_MAX)::type_id
                       ::create("m_cq_mfb_env", this);

        m_mi_config                      = new();
        m_mi_config.addr_base            = 'h0;
        m_mi_config.agent.active         = UVM_ACTIVE;
        m_mi_config.agent.interface_name = "config_mi_vif";
        uvm_config_db #(uvm_mi::regmodel_config)::set(this, "m_regmodel_top", "m_config", m_mi_config);
        m_regmodel_top = uvm_mi::regmodel #(uvm_tx_dma_calypte_regs::regmodel_top #(CHANNELS, DATA_POINTER_WIDTH),
                                            MI_WIDTH, MI_WIDTH)::type_id::create("m_regmodel_top", this);

        m_scoreboard  = scoreboard #(USR_MFB_ITEM_WIDTH, PCIE_CQ_MFB_ITEM_WIDTH, CHANNELS, DATA_POINTER_WIDTH,
                                     USR_MFB_META_WIDTH, DEVICE, UPD_THRESHOLD)::type_id::create("m_scoreboard", this);

        m_sequencer = sequencer #(USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE, USR_MFB_ITEM_WIDTH,
                                  CHANNELS, HDR_META_WIDTH, PKT_SIZE_MAX, DATA_POINTER_WIDTH, PCIE_CQ_MFB_REGIONS,
                                  PCIE_CQ_MFB_REGION_SIZE, PCIE_CQ_MFB_BLOCK_SIZE, PCIE_CQ_MFB_ITEM_WIDTH )::type_id
                      ::create("m_sequencer", this);

        m_tx_mfb_env_cfg                = new;
        m_tx_mfb_env_cfg.active         = UVM_ACTIVE;
        m_tx_mfb_env_cfg.interface_name = "usr_mfb_vif";
        m_tx_mfb_env_cfg.meta_behav     = uvm_logic_vector_array_mfb::config_item::META_SOF;
        uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, "m_tx_mfb_env", "m_config",
                                                                      m_tx_mfb_env_cfg);
        m_tx_mfb_env = uvm_logic_vector_array_mfb::env_tx #(USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE,
                                                            USR_MFB_ITEM_WIDTH, USR_MFB_META_WIDTH)::type_id
                       ::create("m_tx_mfb_env", this);

        m_ptr_upd_mfb_env_cfg                = new;
        m_ptr_upd_mfb_env_cfg.active         = UVM_ACTIVE;
        m_ptr_upd_mfb_env_cfg.interface_name = "ptr_upd_mfb_vif";
        m_ptr_upd_mfb_env_cfg.meta_behav     = uvm_logic_vector_array_mfb::config_item::META_SOF;
        uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, "m_ptr_upd_mfb_env", "m_config",
                                                                      m_ptr_upd_mfb_env_cfg);
        m_ptr_upd_mfb_env = uvm_logic_vector_array_mfb::env_tx #(PCIE_CQ_MFB_REGIONS, PCIE_CQ_MFB_REGION_SIZE,
                                                                 PCIE_CQ_MFB_BLOCK_SIZE, PCIE_CQ_MFB_ITEM_WIDTH,
                                                                 sv_pcie_meta_pack::PCIE_RQ_META_WIDTH)::type_id
                        ::create("m_ptr_upd_mfb_env", this);

        m_upd_stop_req_mvb_env_cfg                = new;
        m_upd_stop_req_mvb_env_cfg.active         = UVM_PASSIVE;
        m_upd_stop_req_mvb_env_cfg.interface_name = "upd_stop_req_mvb_vif";
        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "m_upd_stop_req_mvb_env", "m_config",
                                                                m_upd_stop_req_mvb_env_cfg);
        m_upd_stop_req_mvb_env = uvm_logic_vector_mvb::env_tx #(1, UPD_STOP_REQ_MVB_ITEM_W)::type_id
                                  ::create("m_upd_stop_req_mvb_env", this);

        m_chan_start_req_mvb_env_cfg                = new;
        m_chan_start_req_mvb_env_cfg.active         = UVM_PASSIVE;
        m_chan_start_req_mvb_env_cfg.interface_name = "chan_start_req_mvb_vif";
        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "m_chan_start_req_mvb_env", "m_config",
                                                                m_chan_start_req_mvb_env_cfg);
        m_chan_start_req_mvb_env = uvm_logic_vector_mvb::env_tx #(1, $clog2(CHANNELS))::type_id
                                  ::create("m_chan_start_req_mvb_env", this);

        m_rt_upd_mvb_env_cfg                = new;
        m_rt_upd_mvb_env_cfg.active         = UVM_PASSIVE;
        m_rt_upd_mvb_env_cfg.interface_name = "rt_upd_mvb_vif";
        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "m_rt_upd_mvb_env", "m_config",
                                                                m_rt_upd_mvb_env_cfg);
        m_rt_upd_mvb_env = uvm_logic_vector_mvb::env_tx #(1, RT_UPD_MVB_ITEM_W)::type_id
                                  ::create("m_rt_upd_mvb_env", this);

        m_pkt_drop_meta_mvb_env_cfg                = new;
        m_pkt_drop_meta_mvb_env_cfg.active         = UVM_PASSIVE;
        m_pkt_drop_meta_mvb_env_cfg.interface_name = "pkt_drop_meta_mvb_vif";
        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "m_pkt_drop_meta_mvb_env", "m_config",
                                                                m_pkt_drop_meta_mvb_env_cfg);
        m_pkt_drop_meta_mvb_env = uvm_logic_vector_mvb::env_tx #(PCIE_CQ_MFB_REGIONS, 1)::type_id
                                  ::create("m_pkt_drop_meta_mvb_env", this);
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);
        m_sequencer.m_reset_sqcr              = m_reset_agent.m_sequencer;
        for (int unsigned chan = 0; chan < CHANNELS; chan++) begin
            m_sequencer.m_packet_sqcr[chan]   = m_cq_mfb_env.m_sequencer[chan];
        end
        m_sequencer.m_usr_mfb_sqcr            = m_tx_mfb_env.m_sequencer;
        m_sequencer.m_ptr_upd_mfb_sqcr        = m_ptr_upd_mfb_env.m_sequencer;

        m_cq_mfb_env.m_rx_mfb_env.analysis_port_data.connect(m_scoreboard.m_pcie_cq_data_exp);
        m_cq_mfb_env.m_rx_mfb_env.analysis_port_meta.connect(m_scoreboard.m_pcie_cq_meta_exp);
        m_pkt_drop_meta_mvb_env.analysis_port.connect(m_scoreboard.m_pkt_drop_exp);
        m_tx_mfb_env.analysis_port_data.connect(m_scoreboard.m_usr_data_exp);
        m_tx_mfb_env.analysis_port_meta.connect(m_scoreboard.m_usr_meta_exp);

        m_ptr_upd_mfb_env.analysis_port_data.connect(m_scoreboard.m_ptr_upd_mfb_data_exp);
        m_ptr_upd_mfb_env.analysis_port_meta.connect(m_scoreboard.m_ptr_upd_mfb_meta_exp);
        m_upd_stop_req_mvb_env.analysis_port.connect(m_scoreboard.m_upd_stop_req_mvb_exp);
        m_chan_start_req_mvb_env.analysis_port.connect(m_scoreboard.m_chan_start_req_mvb_exp);
        m_rt_upd_mvb_env.analysis_port.connect(m_scoreboard.m_rt_upd_req_mvb_exp);

        m_scoreboard.regmodel_set(m_regmodel_top.m_regmodel);
        m_cq_mfb_env.regmodel_set(m_regmodel_top.m_regmodel);

        m_cq_mfb_env.m_rx_mfb_env.m_mfb_agent.analysis_port.connect(m_coverage.analysis_export);
        m_reset_agent.sync_connect(m_cq_mfb_env.m_reset_sync);
    endfunction
endclass
