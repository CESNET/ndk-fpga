//-- env.sv: Verification environment
//-- Copyright (C) 2025 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class env #(
    int unsigned RQ_MFB_REGIONS,
    int unsigned RQ_MFB_REGION_SIZE,
    int unsigned RQ_MFB_BLOCK_SIZE,

    int unsigned RC_MFB_REGIONS,
    int unsigned RC_MFB_REGION_SIZE,
    int unsigned RC_MFB_BLOCK_SIZE,

    int unsigned CQ_MFB_REGIONS,
    int unsigned CQ_MFB_REGION_SIZE,
    int unsigned CQ_MFB_BLOCK_SIZE,

    int unsigned CC_MFB_REGIONS,
    int unsigned CC_MFB_REGION_SIZE,
    int unsigned CC_MFB_BLOCK_SIZE,

    string DEVICE
) extends uvm_env;
    `uvm_component_param_utils(uvm_pcie_adapter::env#(
        RQ_MFB_REGIONS, RQ_MFB_REGION_SIZE, RQ_MFB_BLOCK_SIZE,
        RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE,
        CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE,
        CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE,
        DEVICE
    ));

    localparam PCIE_META_TYPE = uvm_pcie_mfb::MFB_META_SOF;
    localparam RQ_STRADDLING = 0;
    localparam CC_STRADDLING = 0;

    sequencer m_sequencer;

    protected uvm_reset::agent m_reset;

    //PCIE INTERFACE
    protected uvm_pcie::root m_pcie;
    // TODO: CRDT Thing if it is not better to put it in pcie_avst interface or
    // pcie_avst_rtile interface
    // use only for intel R-TILE
    // I think this doesn't work corretly
    protected uvm_crdt::tr_planner m_crtd_planner;
    protected uvm_crdt::agent_rx m_crdt_agent_up;
    protected uvm_crdt::agent_tx m_crdt_agent_down;

    //TODO: MFB ROOT
    localparam uvm_pcie_mfb::device_t MFB_DEVICE = (DEVICE == "STRATIX10" || DEVICE == "AGILEX") ?
        uvm_pcie_mfb::DEV_INTEL : uvm_pcie_mfb::DEV_XILINX;
    protected uvm_pcie_mfb::env_rx #(
        RQ_MFB_REGIONS,
        RQ_MFB_REGION_SIZE,
        RQ_MFB_BLOCK_SIZE,
        uvm_pcie_mfb::MFB_RQ,
        PCIE_META_TYPE,
        RQ_STRADDLING,
        MFB_DEVICE
    ) m_mfb_rq_env;
    protected uvm_pcie_mfb::env_tx #(
        RC_MFB_REGIONS,
        RC_MFB_REGION_SIZE,
        RC_MFB_BLOCK_SIZE,
        uvm_pcie_mfb::MFB_RC,
        PCIE_META_TYPE,
        MFB_DEVICE
    ) m_mfb_rc_env;
    protected uvm_pcie_mfb::env_tx #(
        CQ_MFB_REGIONS,
        CQ_MFB_REGION_SIZE,
        CQ_MFB_BLOCK_SIZE,
        uvm_pcie_mfb::MFB_CQ,
        PCIE_META_TYPE,
        MFB_DEVICE
    ) m_mfb_cq_env;
    protected uvm_pcie_mfb::env_rx #(
        CC_MFB_REGIONS,
        CC_MFB_REGION_SIZE,
        CC_MFB_BLOCK_SIZE,
        uvm_pcie_mfb::MFB_CC,
        PCIE_META_TYPE,
        CC_STRADDLING,
        MFB_DEVICE
    ) m_mfb_cc_env;

    //MFB INTERFACE
    protected model      m_model;
    protected scoreboard m_scoreboard;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= (m_model.used() != 0);
        ret |= (m_scoreboard.used() != 0);
        return ret;
    endfunction

    function void build_phase(uvm_phase phase);
        uvm_reset::config_item m_rst_cfg;
        uvm_pcie::config_item  m_pcie_cfg;
        // TODO: CRDT
        uvm_crdt::config_item m_crdt_down_cfg;
        uvm_crdt::config_item m_crdt_up_cfg;

        // COMPONENT SIDE
        uvm_pcie::config_item  m_mfb_rq_cfg;
        uvm_pcie::config_item  m_mfb_rc_cfg;
        uvm_pcie::config_item  m_mfb_cq_cfg;
        uvm_pcie::config_item  m_mfb_cc_cfg;


        super.build_phase(phase);

        m_rst_cfg    = new();
        m_rst_cfg.interface_name    = "vif_reset";
        m_rst_cfg.active    = UVM_ACTIVE;
        uvm_config_db #(uvm_reset::config_item)::set(this, "m_reset", "m_config", m_rst_cfg);
        m_reset = uvm_reset::agent::type_id::create("m_reset", this);

        m_pcie_cfg    = new();
        m_pcie_cfg.interface_name    = "vif_pcie";
        m_pcie_cfg.active    = UVM_ACTIVE;
        uvm_config_db #(uvm_pcie::config_item)::set(this, "m_pcie", "m_config", m_pcie_cfg);
        m_pcie = uvm_pcie::root::type_id::create("m_pcie", this);

        // TODO: CRDT
        m_crdt_down_cfg = new();
        m_crdt_down_cfg.active = UVM_ACTIVE;
        m_crdt_down_cfg.interface_name = "vif_crdt_down";
        uvm_config_db #(uvm_crdt::config_item)::set(this, "m_crdt_agent_down", "m_config", m_crdt_down_cfg);
        m_crdt_agent_down = uvm_crdt::agent_tx::type_id::create("m_crdt_agent_down", this);

        m_crdt_up_cfg = new();
        m_crdt_up_cfg.active = UVM_ACTIVE;
        m_crdt_up_cfg.interface_name = "vif_crdt_up";
        uvm_config_db #(uvm_crdt::config_item)::set(this, "m_crdt_agent_up", "m_config", m_crdt_up_cfg);
        m_crdt_agent_up = uvm_crdt::agent_rx::type_id::create("m_crdt_agent_up", this);

        m_crtd_planner = uvm_crdt::tr_planner::type_id::create("m_crtd_planner", this);

        ////////////////////////////////
        // MFB INTERFACES - USER SIDE
        // TODO: MFB_ROOT
        m_mfb_rq_cfg    = new();
        m_mfb_rq_cfg.interface_name    = "vif_usr_rq";
        m_mfb_rq_cfg.active            = UVM_ACTIVE;
        uvm_config_db #(uvm_pcie::config_item)::set(this, "m_mfb_rq_env", "m_config", m_mfb_rq_cfg);
        m_mfb_rq_env = uvm_pcie_mfb::env_rx #(
            RQ_MFB_REGIONS,
            RQ_MFB_REGION_SIZE,
            RQ_MFB_BLOCK_SIZE,
            uvm_pcie_mfb::MFB_RQ,
            PCIE_META_TYPE,
            RQ_STRADDLING,
            MFB_DEVICE
        )::type_id::create("m_mfb_rq_env", this);

        m_mfb_rc_cfg    = new();
        m_mfb_rc_cfg.interface_name    = "vif_usr_rc";
        m_mfb_rc_cfg.active            = UVM_ACTIVE;
        //m_mfb_rc_cfg.seq_cfg.straddling_set(RC_AXI_STRADDLING);
        uvm_config_db #(uvm_pcie::config_item)::set(this, "m_mfb_rc_env", "m_config", m_mfb_rc_cfg);
        m_mfb_rc_env = uvm_pcie_mfb::env_tx #(
            RC_MFB_REGIONS,
            RC_MFB_REGION_SIZE,
            RC_MFB_BLOCK_SIZE,
            uvm_pcie_mfb::MFB_RC,
            PCIE_META_TYPE,
            MFB_DEVICE
        )::type_id::create("m_mfb_rc_env", this);

        m_mfb_cq_cfg    = new();
        m_mfb_cq_cfg.interface_name  = "vif_usr_cq";
        m_mfb_cq_cfg.active          = UVM_ACTIVE;
        //m_mfb_cq_cfg.seq_cfg.straddling_set(CQ_AXI_STRADDLING);
        uvm_config_db #(uvm_pcie::config_item)::set(this, "m_mfb_cq_env", "m_config", m_mfb_cq_cfg);
        m_mfb_cq_env = uvm_pcie_mfb::env_tx #(
            CQ_MFB_REGIONS,
            CQ_MFB_REGION_SIZE,
            CQ_MFB_BLOCK_SIZE,
            uvm_pcie_mfb::MFB_CQ,
            PCIE_META_TYPE,
            MFB_DEVICE
        )::type_id::create("m_mfb_cq_env", this);

        m_mfb_cc_cfg    = new();
        m_mfb_cc_cfg.interface_name    = "vif_usr_cc";
        m_mfb_cc_cfg.active            = UVM_ACTIVE;
        //m_mfb_cc_cfg.seq_cfg.straddling_set(CC_AXI_STRADDLING);
        uvm_config_db #(uvm_pcie::config_item)::set(this, "m_mfb_cc_env", "m_config", m_mfb_cc_cfg);
        m_mfb_cc_env = uvm_pcie_mfb::env_rx #(
            CC_MFB_REGIONS,
            CC_MFB_REGION_SIZE,
            CC_MFB_BLOCK_SIZE,
            uvm_pcie_mfb::MFB_CC,
            PCIE_META_TYPE,
            CC_STRADDLING,
            MFB_DEVICE
        )::type_id::create("m_mfb_cc_env", this);

        m_model      = model     ::type_id::create("m_model", this);
        m_scoreboard = scoreboard::type_id::create("m_scoreboard", this);

        m_sequencer = sequencer::type_id::create("m_sequencer", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        m_reset.sync_connect(m_pcie.reset_sync);

        // TODO: CRDT
        m_reset.sync_connect(m_crdt_agent_up.reset_sync);
        //m_reset.sync_connect(m_crdt_agent_down.reset_sync);
        m_pcie.analysis_port_rq.connect(m_crtd_planner.analysis_export);
        m_pcie.analysis_port_cc.connect(m_crtd_planner.analysis_export);

        m_reset.sync_connect(m_mfb_rq_env.reset_sync);
        m_reset.sync_connect(m_mfb_rc_env.reset_sync);
        m_reset.sync_connect(m_mfb_cq_env.reset_sync);
        m_reset.sync_connect(m_mfb_cc_env.reset_sync);

        m_sequencer.m_reset   = m_reset.m_sequencer;
        m_sequencer.m_pcie_cq = m_pcie.m_sequencer_cq;
        m_sequencer.m_pcie_rc = m_pcie.m_sequencer_rc;
        m_sequencer.m_mfb_cc  = m_mfb_cc_env.m_sequencer;
        m_sequencer.m_mfb_rq  = m_mfb_rq_env.m_sequencer;

        m_pcie.analysis_port_cq.connect(m_model.m_pcie_cq.analysis_export);
        m_pcie.analysis_port_rc.connect(m_model.m_pcie_rc.analysis_export);
        m_pcie.analysis_port_cc.connect(m_scoreboard.m_pcie_cc.analysis_imp_dut);
        m_pcie.analysis_port_rq.connect(m_scoreboard.m_pcie_rq.analysis_imp_dut);
        m_model.m_mfb_cq.connect    (m_scoreboard.m_mfb_cq.analysis_imp_model);
        m_model.m_mfb_rc.connect    (m_scoreboard.m_mfb_rc.analysis_imp_model);

        m_mfb_rq_env.analysis_port.connect(m_model.m_mfb_rq.analysis_export);
        m_mfb_rc_env.analysis_port.connect(m_scoreboard.m_mfb_rc.analysis_imp_dut);
        m_mfb_cq_env.analysis_port.connect(m_scoreboard.m_mfb_cq.analysis_imp_dut);
        m_mfb_cc_env.analysis_port.connect(m_model.m_mfb_cc.analysis_export);
        m_model.m_pcie_cc.connect    (m_scoreboard.m_pcie_cc.analysis_imp_model);
        m_model.m_pcie_rq.connect    (m_scoreboard.m_pcie_rq.analysis_imp_model);
    endfunction

    // TODO: CRDT
    task run_phase(uvm_phase phase);
        uvm_crdt::sequence_down seq_crdt_down;
        uvm_crdt::sequence_up   seq_crdt_up;


        seq_crdt_down = uvm_crdt::sequence_down::type_id::create("seq_crdt_down", this);
        seq_crdt_down.randomize();

        seq_crdt_up = uvm_crdt::sequence_up::type_id::create("seq_crdt_up", this);
        seq_crdt_up.planner = m_crtd_planner;
        seq_crdt_up.randomize();


        fork
            seq_crdt_down.start(m_crdt_agent_down.m_sequencer);
            seq_crdt_up.start(m_crdt_agent_up.m_sequencer);
        join
    endtask
endclass



