//-- env.sv: Verification environment
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class env #(USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE, USR_MFB_ITEM_WIDTH, PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE, PCIE_RQ_BLOCK_SIZE, PCIE_RQ_ITEM_WIDTH, PCIE_RQ_META_WIDTH, CHANNELS, PKT_SIZE_MAX, MI_WIDTH, DEVICE, POINTER_WIDTH, SW_ADDR_WIDTH) extends uvm_env;
    `uvm_component_param_utils(uvm_dma_ll::env #(USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE, USR_MFB_ITEM_WIDTH, PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE, PCIE_RQ_BLOCK_SIZE, PCIE_RQ_ITEM_WIDTH, PCIE_RQ_META_WIDTH, CHANNELS, PKT_SIZE_MAX, MI_WIDTH, DEVICE, POINTER_WIDTH, SW_ADDR_WIDTH));

    localparam INPUT_META_WIDTH       = 24 + $clog2(PKT_SIZE_MAX+1) + $clog2(CHANNELS);
    localparam PTR_UPD_REQ_MVB_ITEM_W = 2*POINTER_WIDTH + 1 + SW_ADDR_WIDTH;

    sequencer #(USR_MFB_ITEM_WIDTH, PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE, PCIE_RQ_BLOCK_SIZE, PCIE_RQ_ITEM_WIDTH, PCIE_RQ_META_WIDTH, CHANNELS) m_sequencer;
    uvm_reset::agent                                                                                                                            m_reset_agent;
    uvm_dma_ll_rx::env #(USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE, USR_MFB_ITEM_WIDTH, CHANNELS, PKT_SIZE_MAX)                  m_usr_mfb_env;
    uvm_logic_vector_array_mfb::env_tx #(PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE, PCIE_RQ_BLOCK_SIZE, PCIE_RQ_ITEM_WIDTH, PCIE_RQ_META_WIDTH)      m_pcie_rq_mfb_env;
    uvm_mvb::agent_rx #(1, 1)                                                                                                                   m_pkt_disc_mvb_env;
    uvm_mi::regmodel #(regmodel #(CHANNELS), MI_WIDTH, MI_WIDTH)                                                                                m_regmodel;
    scoreboard #(USR_MFB_ITEM_WIDTH, CHANNELS, PKT_SIZE_MAX, PCIE_RQ_META_WIDTH, DEVICE, POINTER_WIDTH, SW_ADDR_WIDTH)                          m_scoreboard;

    uvm_logic_vector_mvb::env_rx #(1, PTR_UPD_REQ_MVB_ITEM_W)                                                                                   m_ptr_upd_req_mvb_env;
    uvm_logic_vector_array_mfb::env_tx #(PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE, PCIE_RQ_BLOCK_SIZE, PCIE_RQ_ITEM_WIDTH, PCIE_RQ_META_WIDTH)      m_ptr_upd_mfb_env;

    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= (m_usr_mfb_env.used() != 0);
        ret |= (m_scoreboard.used() != 0);
        return ret;
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);
        uvm_reset::config_item                  rst_env_conf;
        uvm_dma_ll_rx::config_item              usr_mfb_env_conf;
        uvm_logic_vector_array_mfb::config_item pcie_rq_mfb_env_conf;
        uvm_logic_vector_array_mfb::config_item ptr_upd_mfb_env_conf;
        uvm_logic_vector_mvb::config_item       ptr_upd_req_mvb_env_conf;
        uvm_mvb::config_item                    pkt_disc_mvb_env_conf;
        uvm_mi::regmodel_config                 regmodel_conf;

        rst_env_conf                = new;
        rst_env_conf.active         = UVM_ACTIVE;
        rst_env_conf.interface_name = "reset_vif";
        uvm_config_db #(uvm_reset::config_item)::set(this, "m_reset_agent", "m_config", rst_env_conf);
        m_reset_agent = uvm_reset::agent::type_id::create("m_reset_agent", this);

        usr_mfb_env_conf                = new;
        usr_mfb_env_conf.active         = UVM_ACTIVE;
        usr_mfb_env_conf.interface_name = "usr_mfb_vif";
        uvm_config_db #(uvm_dma_ll_rx::config_item)::set(this, "m_usr_mfb_env", "m_config", usr_mfb_env_conf);
        m_usr_mfb_env = uvm_dma_ll_rx::env #(USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE, USR_MFB_ITEM_WIDTH, CHANNELS, PKT_SIZE_MAX)::type_id::create("m_usr_mfb_env", this);

        pcie_rq_mfb_env_conf                = new;
        pcie_rq_mfb_env_conf.active         = UVM_ACTIVE;
        pcie_rq_mfb_env_conf.interface_name = "pcie_rq_mfb_vif";
        pcie_rq_mfb_env_conf.meta_behav     = uvm_logic_vector_array_mfb::config_item::META_SOF;
        uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, "m_pcie_rq_mfb_env", "m_config", pcie_rq_mfb_env_conf);
        m_pcie_rq_mfb_env    = uvm_logic_vector_array_mfb::env_tx#(PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE, PCIE_RQ_BLOCK_SIZE, PCIE_RQ_ITEM_WIDTH, PCIE_RQ_META_WIDTH)::type_id::create("m_pcie_rq_mfb_env", this);

        ptr_upd_req_mvb_env_conf                = new;
        ptr_upd_req_mvb_env_conf.active         = UVM_PASSIVE;
        ptr_upd_req_mvb_env_conf.interface_name = "ptr_upd_req_mvb_vif";
        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "m_ptr_upd_req_mvb_env", "m_config", ptr_upd_req_mvb_env_conf);
        m_ptr_upd_req_mvb_env = uvm_logic_vector_mvb::env_rx #(1, PTR_UPD_REQ_MVB_ITEM_W)::type_id::create("m_ptr_upd_req_mvb_env", this);

        ptr_upd_mfb_env_conf                = new;
        ptr_upd_mfb_env_conf.active         = UVM_ACTIVE;
        ptr_upd_mfb_env_conf.interface_name = "ptr_upd_mfb_vif";
        ptr_upd_mfb_env_conf.meta_behav     = uvm_logic_vector_array_mfb::config_item::META_SOF;
        uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, "m_ptr_upd_mfb_env", "m_config", ptr_upd_mfb_env_conf);
        m_ptr_upd_mfb_env = uvm_logic_vector_array_mfb::env_tx #(PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE, PCIE_RQ_BLOCK_SIZE, PCIE_RQ_ITEM_WIDTH, PCIE_RQ_META_WIDTH)::type_id::create("m_ptr_upd_mfb_env", this);

        pkt_disc_mvb_env_conf = new;
        pkt_disc_mvb_env_conf.active = UVM_PASSIVE;
        pkt_disc_mvb_env_conf.interface_name = "pkt_disc_mvb_vif";
        uvm_config_db #(uvm_mvb::config_item)::set(this, "m_pkt_disc_mvb_env", "m_config", pkt_disc_mvb_env_conf);
        m_pkt_disc_mvb_env = uvm_mvb::agent_rx#(1, 1)::type_id::create("m_pkt_disc_mvb_env", this);

        regmodel_conf = new();
        regmodel_conf.addr_base            = 'h0;
        regmodel_conf.agent.active         = UVM_ACTIVE;
        regmodel_conf.agent.interface_name = "config_mi_vif";
        uvm_config_db#(uvm_mi::regmodel_config)::set(this, "m_regmodel", "m_config", regmodel_conf);
        m_regmodel = uvm_mi::regmodel#(regmodel#(CHANNELS), MI_WIDTH, MI_WIDTH)::type_id::create("m_regmodel", this);

        m_scoreboard = scoreboard #(USR_MFB_ITEM_WIDTH, CHANNELS, PKT_SIZE_MAX, PCIE_RQ_META_WIDTH, DEVICE, POINTER_WIDTH, SW_ADDR_WIDTH)::type_id::create("m_scoreboard", this);

        m_sequencer = sequencer#(USR_MFB_ITEM_WIDTH, PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE, PCIE_RQ_BLOCK_SIZE, PCIE_RQ_ITEM_WIDTH, PCIE_RQ_META_WIDTH, CHANNELS)::type_id::create("m_sequencer", this);
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);
        m_usr_mfb_env.m_env_rx.analysis_port_data.connect(m_scoreboard.m_usr_mfb_data_exp);
        m_usr_mfb_env.m_env_rx.analysis_port_meta.connect(m_scoreboard.m_usr_mfb_meta_exp);
        m_sequencer.m_reset_sqcr       = m_reset_agent.m_sequencer;
        m_sequencer.m_usr_mfb_sqcr     = m_usr_mfb_env.m_sequencer;
        m_sequencer.m_ptr_upd_mfb_sqcr = m_ptr_upd_mfb_env.m_sequencer;
        m_sequencer.m_pcie_rq_mfb_sqcr = m_pcie_rq_mfb_env.m_sequencer;
        m_sequencer.m_regmodel_sqcr    = m_regmodel.m_regmodel;
        m_scoreboard.regmodel_set(m_regmodel.m_regmodel);
        m_reset_agent.sync_connect(m_usr_mfb_env.reset_sync);

        m_pkt_disc_mvb_env.analysis_port.connect(m_scoreboard.m_pkt_disc_mvb_exp);
        m_pcie_rq_mfb_env.analysis_port_data.connect(m_scoreboard.m_pcie_rq_mfb_data_exp);
        m_pcie_rq_mfb_env.analysis_port_meta.connect(m_scoreboard.m_pcie_rq_mfb_meta_exp);

		m_ptr_upd_req_mvb_env.analysis_port.connect(m_scoreboard.m_ptr_upd_req_mvb_exp);
        m_ptr_upd_mfb_env.analysis_port_data.connect(m_scoreboard.m_ptr_upd_mfb_data_exp);
        m_ptr_upd_mfb_env.analysis_port_meta.connect(m_scoreboard.m_ptr_upd_mfb_meta_exp);

        m_reset_agent.sync_connect(m_usr_mfb_env.reset_sync);
    endfunction
endclass
