//-- env.sv: Verification environment
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class env #(
    int unsigned USR_MFB_REGIONS,
    int unsigned USR_MFB_REGION_SIZE,
    int unsigned USR_MFB_BLOCK_SIZE,
    int unsigned USR_MFB_ITEM_WIDTH,
    int unsigned PCIE_RQ_REGIONS,
    int unsigned PCIE_RQ_REGION_SIZE,
    int unsigned PCIE_RQ_BLOCK_SIZE,
    int unsigned PCIE_RQ_ITEM_WIDTH,
    int unsigned CHANNELS,
    int unsigned PKT_SIZE_MAX,
    int unsigned MI_WIDTH,
    string DEVICE,
    int unsigned POINTER_WIDTH,
    int unsigned SW_ADDR_WIDTH
) extends uvm_env;

    `uvm_component_param_utils(uvm_dma_ll::env #(USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE,
                                                 USR_MFB_ITEM_WIDTH, PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE,
                                                 PCIE_RQ_BLOCK_SIZE, PCIE_RQ_ITEM_WIDTH, CHANNELS,
                                                 PKT_SIZE_MAX, MI_WIDTH, DEVICE, POINTER_WIDTH, SW_ADDR_WIDTH)
    );

    localparam PCIE_DEV               = (DEVICE == "STRATIX10" || DEVICE == "AGILEX") ? uvm_pcie_mfb::DEV_INTEL : uvm_pcie_mfb::DEV_XILINX;
    localparam INPUT_META_WIDTH       = 24 + $clog2(PKT_SIZE_MAX+1) + $clog2(CHANNELS);
    localparam PTR_UPD_REQ_MVB_ITEM_W = 2*POINTER_WIDTH + 1 + SW_ADDR_WIDTH;

    sequencer #(USR_MFB_ITEM_WIDTH, CHANNELS)                                                     m_sequencer;
    uvm_reset::agent                                                                              m_reset_agent;
    uvm_dma_ll_rx::env #(USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE, USR_MFB_ITEM_WIDTH,
                         CHANNELS, PKT_SIZE_MAX
    ) m_usr_mfb_env;
    uvm_pcie_mfb::env_tx #(
            PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE, PCIE_RQ_BLOCK_SIZE,
            uvm_pcie_mfb::MFB_RQ, uvm_pcie_mfb::MFB_META_SOF, PCIE_DEV
    ) m_pcie_rq;
    uvm_mi::regmodel #(regmodel #(CHANNELS), MI_WIDTH, MI_WIDTH)                                  m_regmodel;
    scoreboard #(USR_MFB_ITEM_WIDTH, CHANNELS, PKT_SIZE_MAX, DEVICE, POINTER_WIDTH,
                 SW_ADDR_WIDTH)                                                                   m_scoreboard;


    uvm_logic_vector_mvb::env_rx #(1, PTR_UPD_REQ_MVB_ITEM_W)                                     m_ptr_upd_req_mvb_env;
    uvm_pcie_mfb::env_tx #(
            PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE, PCIE_RQ_BLOCK_SIZE,
            uvm_pcie_mfb::MFB_RQ, uvm_pcie_mfb::MFB_META_SOF, PCIE_DEV
    ) m_pcie_rq_upd;

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
        uvm_reset::config_item            rst_env_conf;
        uvm_dma_ll_rx::config_item        usr_mfb_env_conf;
        uvm_pcie::config_item             pcie_rq_mfb_env_conf;
        uvm_pcie::config_item             ptr_upd_mfb_env_conf;
        uvm_logic_vector_mvb::config_item ptr_upd_req_mvb_env_conf;
        uvm_mvb::config_item              pkt_disc_mvb_env_conf;
        uvm_mi::regmodel_config           regmodel_conf;

        rst_env_conf                = new;
        rst_env_conf.active         = UVM_ACTIVE;
        rst_env_conf.interface_name = "reset_vif";
        uvm_config_db #(uvm_reset::config_item)::set(this, "m_reset_agent", "m_config", rst_env_conf);
        m_reset_agent = uvm_reset::agent::type_id::create("m_reset_agent", this);

        usr_mfb_env_conf                = new;
        usr_mfb_env_conf.active         = UVM_ACTIVE;
        usr_mfb_env_conf.interface_name = "usr_mfb_vif";
        uvm_config_db #(uvm_dma_ll_rx::config_item)::set(this, "m_usr_mfb_env", "m_config", usr_mfb_env_conf);
        m_usr_mfb_env = uvm_dma_ll_rx
                        ::env #(USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE, USR_MFB_ITEM_WIDTH, CHANNELS,
                                PKT_SIZE_MAX)::type_id::create("m_usr_mfb_env", this);

        pcie_rq_mfb_env_conf                = new;
        pcie_rq_mfb_env_conf.active         = UVM_ACTIVE;
        pcie_rq_mfb_env_conf.interface_name = "pcie_rq_mfb_vif";
        //pcie_rq_mfb_env_conf.meta_behav     = uvm_logic_vector_array_mfb::config_item::META_SOF;
        uvm_config_db #(uvm_pcie::config_item)::set(this, "m_pcie_rq", "m_config", pcie_rq_mfb_env_conf);
        m_pcie_rq = uvm_pcie_mfb::env_tx #(
            PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE, PCIE_RQ_BLOCK_SIZE,
            uvm_pcie_mfb::MFB_RQ, uvm_pcie_mfb::MFB_META_SOF, PCIE_DEV
        )::type_id::create("m_pcie_rq", this);


        ptr_upd_req_mvb_env_conf                = new;
        ptr_upd_req_mvb_env_conf.active         = UVM_PASSIVE;
        ptr_upd_req_mvb_env_conf.interface_name = "ptr_upd_req_mvb_vif";
        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "m_ptr_upd_req_mvb_env", "m_config",
                                                                ptr_upd_req_mvb_env_conf);
        m_ptr_upd_req_mvb_env = uvm_logic_vector_mvb::env_rx #(1, PTR_UPD_REQ_MVB_ITEM_W)::type_id
                                ::create("m_ptr_upd_req_mvb_env", this);

        ptr_upd_mfb_env_conf                = new;
        ptr_upd_mfb_env_conf.active         = UVM_ACTIVE;
        ptr_upd_mfb_env_conf.interface_name = "ptr_upd_mfb_vif";
        //ptr_upd_mfb_env_conf.meta_behav     = uvm_logic_vector_array_mfb::config_item::META_SOF;
        uvm_config_db #(uvm_pcie::config_item)::set(this, "m_pcie_rq_upd", "m_config",
                                                                      ptr_upd_mfb_env_conf);
        m_pcie_rq_upd = uvm_pcie_mfb::env_tx #(
            PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE, PCIE_RQ_BLOCK_SIZE,
            uvm_pcie_mfb::MFB_RQ, uvm_pcie_mfb::MFB_META_SOF, PCIE_DEV
        )::type_id::create("m_pcie_rq_upd", this);

        regmodel_conf = new();
        regmodel_conf.addr_base            = 'h0;
        regmodel_conf.agent.active         = UVM_ACTIVE;
        regmodel_conf.agent.interface_name = "config_mi_vif";
        uvm_config_db#(uvm_mi::regmodel_config)::set(this, "m_regmodel", "m_config", regmodel_conf);
        m_regmodel = uvm_mi::regmodel#(regmodel#(CHANNELS), MI_WIDTH, MI_WIDTH)::type_id::create("m_regmodel", this);

        m_scoreboard = scoreboard #(USR_MFB_ITEM_WIDTH, CHANNELS, PKT_SIZE_MAX, DEVICE,
                                    POINTER_WIDTH, SW_ADDR_WIDTH)::type_id::create("m_scoreboard", this);

        m_sequencer = sequencer #(USR_MFB_ITEM_WIDTH, CHANNELS)::type_id::create("m_sequencer", this);
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);
        m_usr_mfb_env.m_env_rx.analysis_port_data.connect(m_scoreboard.m_usr_mfb_data_exp);
        m_usr_mfb_env.m_env_rx.analysis_port_meta.connect(m_scoreboard.m_usr_mfb_meta_exp);
        m_sequencer.m_reset_sqcr       = m_reset_agent.m_sequencer;
        m_sequencer.m_usr_mfb_sqcr     = m_usr_mfb_env.m_sequencer;
        m_sequencer.m_regmodel_sqcr    = m_regmodel.m_regmodel;
        m_scoreboard.regmodel_set(m_regmodel.m_regmodel);
        m_reset_agent.sync_connect(m_usr_mfb_env.reset_sync);

        m_pcie_rq.analysis_port.connect(m_scoreboard.m_pcie_rq_data_dut);

        m_ptr_upd_req_mvb_env.analysis_port.connect(m_scoreboard.m_ptr_upd_req_mvb_exp);
        m_pcie_rq_upd.analysis_port.connect(m_scoreboard.m_pcie_rq_upd_dut);

        m_reset_agent.sync_connect(m_usr_mfb_env.reset_sync);
    endfunction
endclass
