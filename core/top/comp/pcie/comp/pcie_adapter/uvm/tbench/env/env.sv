//-- env.sv: Verification environment
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class env #(CQ_MFB_REGIONS, CC_MFB_REGIONS, RQ_MFB_REGIONS, RC_MFB_REGIONS, CQ_MFB_REGION_SIZE, CC_MFB_REGION_SIZE, RQ_MFB_REGION_SIZE, RC_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, CC_MFB_BLOCK_SIZE, RQ_MFB_BLOCK_SIZE, RC_MFB_BLOCK_SIZE, CQ_MFB_ITEM_WIDTH, CC_MFB_ITEM_WIDTH, RQ_MFB_ITEM_WIDTH, RC_MFB_ITEM_WIDTH, AVST_DOWN_META_W, AVST_UP_META_W, AXI_CQUSER_WIDTH, AXI_CCUSER_WIDTH, AXI_RCUSER_WIDTH, AXI_RQUSER_WIDTH, AXI_DATA_WIDTH, RQ_MFB_META_W, RC_MFB_META_W, CQ_MFB_META_W, CC_MFB_META_W, DEVICE, ENDPOINT_TYPE, READY_LATENCY, AXI_STRADDLING) extends uvm_env;

    `uvm_component_param_utils(uvm_pcie_adapter::env #(CQ_MFB_REGIONS, CC_MFB_REGIONS, RQ_MFB_REGIONS, RC_MFB_REGIONS, CQ_MFB_REGION_SIZE, CC_MFB_REGION_SIZE, RQ_MFB_REGION_SIZE, RC_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, CC_MFB_BLOCK_SIZE, RQ_MFB_BLOCK_SIZE, RC_MFB_BLOCK_SIZE, CQ_MFB_ITEM_WIDTH, CC_MFB_ITEM_WIDTH, RQ_MFB_ITEM_WIDTH, RC_MFB_ITEM_WIDTH, AVST_DOWN_META_W, AVST_UP_META_W, AXI_CQUSER_WIDTH, AXI_CCUSER_WIDTH, AXI_RCUSER_WIDTH, AXI_RQUSER_WIDTH, AXI_DATA_WIDTH, RQ_MFB_META_W, RC_MFB_META_W, CQ_MFB_META_W, CC_MFB_META_W, DEVICE, ENDPOINT_TYPE, READY_LATENCY, AXI_STRADDLING));

    localparam IS_INTEL_DEV = (DEVICE == "STRATIX10" || DEVICE == "AGILEX");
    localparam RC_AXI_STRADDLING = 1;
    localparam RQ_AXI_STRADDLING = (AXI_RQUSER_WIDTH == 137) ? 1 : 0;
    // Not yet supported
    localparam CC_AXI_STRADDLING = 0;
    localparam CQ_AXI_STRADDLING = (AXI_CQUSER_WIDTH == 183 && AXI_STRADDLING) ? 1 : 0;

    generator #(CQ_MFB_ITEM_WIDTH, AVST_DOWN_META_W, "DOWN", ENDPOINT_TYPE, "DOWN") m_avst_down_generator;
    generator #(CC_MFB_ITEM_WIDTH, CC_MFB_META_W, "UP", ENDPOINT_TYPE, "CC")      m_cc_generator;
    generator #(RQ_MFB_ITEM_WIDTH, RQ_MFB_META_W, "UP", ENDPOINT_TYPE, "RQ")      m_rq_generator;
    monitor #(CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, CC_MFB_ITEM_WIDTH, AVST_UP_META_W)                                               m_monitor;
    tr_planner #(CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, CC_MFB_ITEM_WIDTH, AVST_UP_META_W)                                            m_tr_plan;

    // AVALON interface (INTEL)
    uvm_logic_vector_array_avst::env_rx #(CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, CQ_MFB_ITEM_WIDTH, AVST_DOWN_META_W, READY_LATENCY) m_avst_down_env;
    uvm_logic_vector_array_avst::env_tx #(CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, CC_MFB_ITEM_WIDTH, AVST_UP_META_W  , 3) m_avst_up_env;
    // Credit Control (INTEL)
    uvm_crdt::agent_rx m_crdt_agent_up;
    uvm_crdt::agent_tx m_crdt_agent_down;
    // AXI interface (XILINX)
    uvm_logic_vector_array_axi::env_rx #(AXI_DATA_WIDTH, AXI_CQUSER_WIDTH, CQ_MFB_ITEM_WIDTH, CQ_MFB_REGIONS, CQ_MFB_BLOCK_SIZE, CQ_AXI_STRADDLING)     m_axi_cq_env;
    uvm_logic_vector_array_axi::env_tx #(AXI_DATA_WIDTH, AXI_CCUSER_WIDTH, CC_MFB_ITEM_WIDTH, CC_MFB_REGIONS, CC_MFB_BLOCK_SIZE, CC_AXI_STRADDLING)     m_axi_cc_env;
    uvm_logic_vector_array_axi::env_rx #(AXI_DATA_WIDTH, AXI_RCUSER_WIDTH, RC_MFB_ITEM_WIDTH, RC_MFB_REGIONS, RC_MFB_BLOCK_SIZE, RC_AXI_STRADDLING)     m_axi_rc_env;
    uvm_logic_vector_array_axi::env_tx #(AXI_DATA_WIDTH, AXI_RQUSER_WIDTH, RQ_MFB_ITEM_WIDTH, RQ_MFB_REGIONS, RQ_MFB_BLOCK_SIZE, RQ_AXI_STRADDLING)     m_axi_rq_env;
    // MFB interface (XILINX and INTEL)
    uvm_logic_vector_array_mfb::env_rx #(RQ_MFB_REGIONS, RQ_MFB_REGION_SIZE, RQ_MFB_BLOCK_SIZE, RQ_MFB_ITEM_WIDTH, RQ_MFB_META_W)                    m_mfb_rq_env;
    uvm_logic_vector_array_mfb::env_tx #(RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, RC_MFB_ITEM_WIDTH, RC_MFB_META_W)                    m_mfb_rc_env;
    uvm_logic_vector_array_mfb::env_tx #(CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, CQ_MFB_ITEM_WIDTH, CQ_MFB_META_W)                    m_mfb_cq_env;
    uvm_logic_vector_array_mfb::env_rx #(CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, CC_MFB_ITEM_WIDTH, CC_MFB_META_W)                    m_mfb_cc_env;
    // Reset agent
    uvm_reset::agent m_reset;
    uvm_logic_vector_array::agent#(RQ_MFB_ITEM_WIDTH) m_byte_array_agent_rq;
    uvm_logic_vector_array::agent#(CC_MFB_ITEM_WIDTH) m_byte_array_agent_cc;
    uvm_logic_vector_array::agent#(CQ_MFB_ITEM_WIDTH) m_byte_array_agent_down;

    // Avalon configuration
    uvm_logic_vector_array_avst::config_item m_avst_down_cfg;
    uvm_logic_vector_array_avst::config_item m_avst_up_cfg;
    // Credit Control configuration
    uvm_crdt::config_item               m_crdt_down_cfg;
    uvm_crdt::config_item               m_crdt_up_cfg;
    // AXI configuration
    uvm_logic_vector_array_axi::config_item  m_axi_cq_cfg;
    uvm_logic_vector_array_axi::config_item  m_axi_cc_cfg;
    uvm_logic_vector_array_axi::config_item  m_axi_rc_cfg;
    uvm_logic_vector_array_axi::config_item  m_axi_rq_cfg;
    // MFB configuration
    uvm_logic_vector_array_mfb::config_item  m_rq_mfb_cfg;
    uvm_logic_vector_array_mfb::config_item  m_rc_mfb_cfg;
    uvm_logic_vector_array_mfb::config_item  m_cq_mfb_cfg;
    uvm_logic_vector_array_mfb::config_item  m_cc_mfb_cfg;
    // Reset configuration
    uvm_reset::config_item                   m_reset_cfg;
    // DATA AGENTS
    uvm_logic_vector_array::config_item      m_byte_array_agent_rq_cfg;
    uvm_logic_vector_array::config_item      m_byte_array_agent_cc_cfg;
    uvm_logic_vector_array::config_item      m_byte_array_agent_down_cfg;

    uvm_pcie_adapter::virt_sequencer#(CQ_MFB_REGIONS, CC_MFB_REGIONS, RQ_MFB_REGIONS, RC_MFB_REGIONS, CQ_MFB_REGION_SIZE, CC_MFB_REGION_SIZE, RQ_MFB_REGION_SIZE, RC_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, CC_MFB_BLOCK_SIZE, RQ_MFB_BLOCK_SIZE, RC_MFB_BLOCK_SIZE, CQ_MFB_ITEM_WIDTH, CC_MFB_ITEM_WIDTH, RQ_MFB_ITEM_WIDTH, RC_MFB_ITEM_WIDTH, AVST_DOWN_META_W, AVST_UP_META_W, AXI_CQUSER_WIDTH, AXI_CCUSER_WIDTH, AXI_RCUSER_WIDTH, AXI_RQUSER_WIDTH, AXI_DATA_WIDTH, RQ_MFB_META_W, RC_MFB_META_W, CQ_MFB_META_W, CC_MFB_META_W) vscr;

    scoreboard #(CQ_MFB_ITEM_WIDTH, CC_MFB_ITEM_WIDTH, RQ_MFB_ITEM_WIDTH, RC_MFB_ITEM_WIDTH, AVST_DOWN_META_W, AVST_UP_META_W, AXI_CQUSER_WIDTH, AXI_CCUSER_WIDTH, AXI_RCUSER_WIDTH, AXI_RQUSER_WIDTH, RQ_MFB_META_W, RC_MFB_META_W, CQ_MFB_META_W, CC_MFB_META_W, DEVICE, ENDPOINT_TYPE, CC_MFB_BLOCK_SIZE) m_scoreboard;

    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);

        m_byte_array_agent_cc_cfg          = new();
        m_byte_array_agent_rq_cfg          = new();
        m_byte_array_agent_down_cfg        = new();
        m_byte_array_agent_cc_cfg.active   = UVM_ACTIVE;
        m_byte_array_agent_rq_cfg.active   = UVM_ACTIVE;
        m_byte_array_agent_down_cfg.active = UVM_ACTIVE;

        uvm_config_db #(uvm_logic_vector_array::config_item)::set(this, "m_byte_array_agent_cc", "m_config", m_byte_array_agent_cc_cfg);
        uvm_config_db #(uvm_logic_vector_array::config_item)::set(this, "m_byte_array_agent_rq", "m_config", m_byte_array_agent_rq_cfg);
        uvm_config_db #(uvm_logic_vector_array::config_item)::set(this, "m_byte_array_agent_down", "m_config", m_byte_array_agent_down_cfg);

        m_byte_array_agent_cc = uvm_logic_vector_array::agent#(RQ_MFB_ITEM_WIDTH)::type_id::create("m_byte_array_agent_cc", this);
        m_byte_array_agent_rq = uvm_logic_vector_array::agent#(CC_MFB_ITEM_WIDTH)::type_id::create("m_byte_array_agent_rq", this);
        m_byte_array_agent_down = uvm_logic_vector_array::agent#(CQ_MFB_ITEM_WIDTH)::type_id::create("m_byte_array_agent_down", this);

        // AVALON configuratiom
        m_avst_down_cfg = new();
        m_avst_up_cfg   = new();
        // Credit Control configuration
        m_crdt_down_cfg = new();
        m_crdt_up_cfg   = new();
        // AXI configuratiom
        m_axi_cq_cfg    = new();
        m_axi_cc_cfg    = new();
        m_axi_rc_cfg    = new();
        m_axi_rq_cfg    = new();
        // MFB configuratiom
        m_rq_mfb_cfg    = new();
        m_rc_mfb_cfg    = new();
        m_cq_mfb_cfg    = new();
        m_cc_mfb_cfg    = new();
        m_reset_cfg     = new();

        // AVALON configuratiom
        m_avst_down_cfg.active = UVM_ACTIVE;
        m_avst_up_cfg.active   = UVM_ACTIVE;
        // Credit Control configuration
        m_crdt_down_cfg.active = UVM_ACTIVE;
        m_crdt_up_cfg.active   = UVM_ACTIVE;
        // AXI configuratiom
        m_axi_cq_cfg.active    = UVM_ACTIVE;
        m_axi_cc_cfg.active    = UVM_ACTIVE;
        m_axi_rc_cfg.active    = UVM_ACTIVE;
        m_axi_rq_cfg.active    = UVM_ACTIVE;
        // MFB configuratiom
        m_rq_mfb_cfg.active    = UVM_ACTIVE;
        m_rc_mfb_cfg.active    = UVM_ACTIVE;
        m_cq_mfb_cfg.active    = UVM_ACTIVE;
        m_cc_mfb_cfg.active    = UVM_ACTIVE;
        m_reset_cfg.active     = UVM_ACTIVE;

        // AVALON configuratiom
        m_avst_down_cfg.interface_name = "vif_avst_down";
        m_avst_up_cfg.interface_name   = "vif_avst_up";
        // Credit Control configuration
        m_crdt_down_cfg.interface_name = "vif_crdt_down";
        m_crdt_up_cfg.interface_name   = "vif_crdt_up";
        // AXI configuratiom
        m_axi_cq_cfg.interface_name    = "vif_cq_axi";
        m_axi_cc_cfg.interface_name    = "vif_cc_axi";
        m_axi_rc_cfg.interface_name    = "vif_rc_axi";
        m_axi_rq_cfg.interface_name    = "vif_rq_axi";
        // MFB configuratiom
        m_rq_mfb_cfg.interface_name    = "vif_rq_mfb";
        m_rc_mfb_cfg.interface_name    = "vif_rc_mfb";
        m_cq_mfb_cfg.interface_name    = "vif_cq_mfb";
        m_cc_mfb_cfg.interface_name    = "vif_cc_mfb";
        m_reset_cfg.interface_name     = "vif_reset";

        // AVALON configuratiom
        m_avst_down_cfg.meta_behav = uvm_logic_vector_array_avst::config_item::META_SOF;
        m_avst_up_cfg.meta_behav   = uvm_logic_vector_array_avst::config_item::META_SOF;
        // MFB configuratiom
        m_rq_mfb_cfg.meta_behav    = (IS_INTEL_DEV) ? uvm_logic_vector_array_mfb::config_item::META_SOF : uvm_logic_vector_array_mfb::config_item::META_NONE;
        m_rc_mfb_cfg.meta_behav    = (IS_INTEL_DEV) ? uvm_logic_vector_array_mfb::config_item::META_SOF : uvm_logic_vector_array_mfb::config_item::META_NONE;
        m_cq_mfb_cfg.meta_behav    = (IS_INTEL_DEV) ? uvm_logic_vector_array_mfb::config_item::META_SOF : uvm_logic_vector_array_mfb::config_item::META_NONE;
        m_cc_mfb_cfg.meta_behav    = (IS_INTEL_DEV) ? uvm_logic_vector_array_mfb::config_item::META_SOF : uvm_logic_vector_array_mfb::config_item::META_NONE;

        // MFB RQ
        m_rq_mfb_cfg.seq_type = "PCIE";
        // MFB RC
        m_rc_mfb_cfg.seq_type = "PCIE";
        // MFB CQ
        m_cq_mfb_cfg.seq_type = "PCIE";
        // MFB CC
        m_cc_mfb_cfg.seq_type = "PCIE";

        // MFB RQ
        m_rq_mfb_cfg.seq_cfg  = new();
        m_rq_mfb_cfg.seq_cfg.straddling_set(RQ_AXI_STRADDLING);
        // MFB RC
        m_rc_mfb_cfg.seq_cfg  = new();
        m_rc_mfb_cfg.seq_cfg.straddling_set(AXI_STRADDLING);
        // MFB CQ
        m_cq_mfb_cfg.seq_cfg  = new();
        m_cq_mfb_cfg.seq_cfg.straddling_set(AXI_STRADDLING);
        // MFB CC
        m_cc_mfb_cfg.seq_cfg  = new();
        m_cc_mfb_cfg.seq_cfg.straddling_set(CC_AXI_STRADDLING);
        // AVST DOWN
        m_avst_down_cfg.seq_cfg = new();
        m_avst_down_cfg.seq_cfg.straddling_set(1);
        // AVST UP
        m_avst_up_cfg.seq_cfg = new();
        m_avst_up_cfg.seq_cfg.straddling_set(1);

        // AVALON
        uvm_config_db #(uvm_logic_vector_array_avst::config_item)::set(this, "m_avst_down_env", "m_config", m_avst_down_cfg);
        uvm_config_db #(uvm_logic_vector_array_avst::config_item)::set(this, "m_avst_up_env", "m_config", m_avst_up_cfg);
        // Credit Control
        uvm_config_db #(uvm_crdt::config_item)::set(this, "m_crdt_agent_up", "m_config", m_crdt_up_cfg);
        uvm_config_db #(uvm_crdt::config_item)::set(this, "m_crdt_agent_down", "m_config", m_crdt_down_cfg);
        // AXI
        uvm_config_db #(uvm_logic_vector_array_axi::config_item)::set(this, "m_axi_cq_env", "m_config", m_axi_cq_cfg);
        uvm_config_db #(uvm_logic_vector_array_axi::config_item)::set(this, "m_axi_cc_env", "m_config", m_axi_cc_cfg);
        uvm_config_db #(uvm_logic_vector_array_axi::config_item)::set(this, "m_axi_rc_env", "m_config", m_axi_rc_cfg);
        uvm_config_db #(uvm_logic_vector_array_axi::config_item)::set(this, "m_axi_rq_env", "m_config", m_axi_rq_cfg);
        // MFB
        uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, "m_mfb_rq_env", "m_config", m_rq_mfb_cfg);
        uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, "m_mfb_rc_env", "m_config", m_rc_mfb_cfg);
        uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, "m_mfb_cq_env", "m_config", m_cq_mfb_cfg);
        uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, "m_mfb_cc_env", "m_config", m_cc_mfb_cfg);
        // Reset
        uvm_config_db #(uvm_reset::config_item)::set(this, "m_reset", "m_config", m_reset_cfg);

        // Create AVALON environments
        m_avst_down_env = uvm_logic_vector_array_avst::env_rx #(CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, CQ_MFB_ITEM_WIDTH, AVST_DOWN_META_W, READY_LATENCY)::type_id::create("m_avst_down_env", this);
        m_avst_up_env   = uvm_logic_vector_array_avst::env_tx #(CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, CC_MFB_ITEM_WIDTH, AVST_UP_META_W  , 3)::type_id::create("m_avst_up_env", this);
        // Credit Control agent
        m_crdt_agent_up   = uvm_crdt::agent_rx::type_id::create("m_crdt_agent_up", this);
        m_crdt_agent_down = uvm_crdt::agent_tx::type_id::create("m_crdt_agent_down", this);
        // Create AXI environments
        m_axi_cq_env    = uvm_logic_vector_array_axi::env_rx #(AXI_DATA_WIDTH, AXI_CQUSER_WIDTH, CQ_MFB_ITEM_WIDTH, CQ_MFB_REGIONS, CQ_MFB_BLOCK_SIZE, CQ_AXI_STRADDLING)::type_id::create("m_axi_cq_env", this);
        m_axi_cc_env    = uvm_logic_vector_array_axi::env_tx #(AXI_DATA_WIDTH, AXI_CCUSER_WIDTH, CC_MFB_ITEM_WIDTH, CC_MFB_REGIONS, CC_MFB_BLOCK_SIZE, CC_AXI_STRADDLING)::type_id::create("m_axi_cc_env", this);
        m_axi_rc_env    = uvm_logic_vector_array_axi::env_rx #(AXI_DATA_WIDTH, AXI_RCUSER_WIDTH, RC_MFB_ITEM_WIDTH, RC_MFB_REGIONS, RC_MFB_BLOCK_SIZE, RC_AXI_STRADDLING)::type_id::create("m_axi_rc_env", this);
        m_axi_rq_env    = uvm_logic_vector_array_axi::env_tx #(AXI_DATA_WIDTH, AXI_RQUSER_WIDTH, RQ_MFB_ITEM_WIDTH, RQ_MFB_REGIONS, RQ_MFB_BLOCK_SIZE, RQ_AXI_STRADDLING)::type_id::create("m_axi_rq_env", this);
        // Create MFB environments
        m_mfb_rq_env    = uvm_logic_vector_array_mfb::env_rx #(RQ_MFB_REGIONS, RQ_MFB_REGION_SIZE, RQ_MFB_BLOCK_SIZE, RQ_MFB_ITEM_WIDTH, RQ_MFB_META_W)::type_id::create("m_mfb_rq_env", this);
        m_mfb_rc_env    = uvm_logic_vector_array_mfb::env_tx #(RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, RC_MFB_ITEM_WIDTH, RC_MFB_META_W)::type_id::create("m_mfb_rc_env", this);
        m_mfb_cq_env    = uvm_logic_vector_array_mfb::env_tx #(CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, CQ_MFB_ITEM_WIDTH, CQ_MFB_META_W)::type_id::create("m_mfb_cq_env", this);
        m_mfb_cc_env    = uvm_logic_vector_array_mfb::env_rx #(CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, CC_MFB_ITEM_WIDTH, CC_MFB_META_W)::type_id::create("m_mfb_cc_env", this);
        // Create Reset agent
        m_reset = uvm_reset::agent::type_id::create("m_reset", this);

        m_scoreboard = scoreboard #(CQ_MFB_ITEM_WIDTH, CC_MFB_ITEM_WIDTH, RQ_MFB_ITEM_WIDTH, RC_MFB_ITEM_WIDTH, AVST_DOWN_META_W, AVST_UP_META_W, AXI_CQUSER_WIDTH, AXI_CCUSER_WIDTH, AXI_RCUSER_WIDTH, AXI_RQUSER_WIDTH, RQ_MFB_META_W, RC_MFB_META_W, CQ_MFB_META_W, CC_MFB_META_W, DEVICE, ENDPOINT_TYPE, CC_MFB_BLOCK_SIZE)::type_id::create("m_scoreboard", this);
        vscr         = uvm_pcie_adapter::virt_sequencer#(CQ_MFB_REGIONS, CC_MFB_REGIONS, RQ_MFB_REGIONS, RC_MFB_REGIONS, CQ_MFB_REGION_SIZE, CC_MFB_REGION_SIZE, RQ_MFB_REGION_SIZE, RC_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, CC_MFB_BLOCK_SIZE, RQ_MFB_BLOCK_SIZE, RC_MFB_BLOCK_SIZE, CQ_MFB_ITEM_WIDTH, CC_MFB_ITEM_WIDTH, RQ_MFB_ITEM_WIDTH, RC_MFB_ITEM_WIDTH, AVST_DOWN_META_W, AVST_UP_META_W, AXI_CQUSER_WIDTH, AXI_CCUSER_WIDTH, AXI_RCUSER_WIDTH, AXI_RQUSER_WIDTH, AXI_DATA_WIDTH, RQ_MFB_META_W, RC_MFB_META_W, CQ_MFB_META_W, CC_MFB_META_W)::type_id::create("vscr",this);

        if (IS_INTEL_DEV) begin
            if (m_avst_down_cfg.active == UVM_ACTIVE) begin
                m_avst_down_generator    = generator #(CQ_MFB_ITEM_WIDTH, AVST_DOWN_META_W, "DOWN", ENDPOINT_TYPE, "DOWN")::type_id::create("m_avst_down_generator", this);
            end
            if (m_cc_mfb_cfg.active == UVM_ACTIVE) begin
                m_cc_generator    = generator #(CC_MFB_ITEM_WIDTH, CC_MFB_META_W, "UP", ENDPOINT_TYPE, "CC")::type_id::create("m_cc_generator", this);
            end
            if (m_rq_mfb_cfg.active == UVM_ACTIVE) begin
                m_rq_generator    = generator #(RQ_MFB_ITEM_WIDTH, RQ_MFB_META_W, "UP", ENDPOINT_TYPE, "RQ")::type_id::create("m_rq_generator", this);
            end
            m_monitor = monitor #(CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, CC_MFB_ITEM_WIDTH, AVST_UP_META_W)::type_id::create("m_monitor", this);
        end
        m_tr_plan = tr_planner #(CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, CC_MFB_ITEM_WIDTH, AVST_UP_META_W)::type_id::create("m_tr_plan", this);

    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);

        // ------------------------------------------------------------------
        // Connection to the Scoreboard
        // ------------------------------------------------------------------

        // Connect AVALON environments to Scoreboard
        if (IS_INTEL_DEV) begin
            // DOWN environment
            m_avst_down_env.analysis_port_data.connect(m_scoreboard.analysis_imp_avst_down_data);
            m_avst_down_env.analysis_port_meta.connect(m_scoreboard.analysis_imp_avst_down_meta);
            // UP environment
            m_avst_up_env.analysis_port_data.connect(m_scoreboard.analysis_imp_avst_up_data);
            m_avst_up_env.analysis_port_meta.connect(m_scoreboard.analysis_imp_avst_up_meta);

            m_mfb_rq_env.analysis_port_meta.connect(m_scoreboard.analysis_imp_mfb_rq_meta);
            m_mfb_cc_env.analysis_port_meta.connect(m_scoreboard.analysis_imp_mfb_cc_meta);

            m_mfb_rc_env.analysis_port_meta.connect(m_scoreboard.analysis_imp_mfb_rc_meta);
            m_mfb_cq_env.analysis_port_meta.connect(m_scoreboard.analysis_imp_mfb_cq_meta);

            m_avst_up_env.m_avst_agent.analysis_port.connect(m_monitor.analysis_export);
            m_monitor.analysis_port.connect(m_tr_plan.analysis_imp);

            if (m_avst_down_cfg.active == UVM_ACTIVE) begin
                // Connect AVALON environments to data Sequencer
                m_avst_down_generator.seq_item_port_data.connect(m_byte_array_agent_down.m_sequencer.seq_item_export);
                vscr.m_avst_down_data_sqr = m_byte_array_agent_down.m_sequencer;
            end
            if (m_cc_mfb_cfg.active == UVM_ACTIVE) begin
                m_cc_generator.seq_item_port_data.connect(m_byte_array_agent_cc.m_sequencer.seq_item_export);
                vscr.m_cc_mfb_data_sqr = m_byte_array_agent_cc.m_sequencer;
            end
            if (m_rq_mfb_cfg.active == UVM_ACTIVE) begin
                m_rq_generator.seq_item_port_data.connect(m_byte_array_agent_rq.m_sequencer.seq_item_export);
                vscr.m_rq_mfb_data_sqr = m_byte_array_agent_rq.m_sequencer;
            end

            // Connect Credit Control agent to sequencers
            vscr.m_crdt_up_sqr   = m_crdt_agent_up.m_sequencer;
            vscr.m_crdt_down_sqr = m_crdt_agent_down.m_sequencer;

            // Connect AVALON environments to READY Sequencer
            vscr.m_avst_up_rdy_sqr = m_avst_up_env.m_sequencer;

        end else begin
            // Connect AXI environments to Scoreboard
            // CQ environment
            m_axi_cq_env.analysis_port_data.connect(m_scoreboard.analysis_imp_axi_cq_data);
            // CC environment
            m_axi_cc_env.analysis_port_data.connect(m_scoreboard.analysis_imp_axi_cc_data);
            // RC environment
            m_axi_rc_env.analysis_port_data.connect(m_scoreboard.analysis_imp_axi_rc_data);
            // RQ environment
            m_axi_rq_env.analysis_port_data.connect(m_scoreboard.analysis_imp_axi_rq_data);

            // Connect MFB environments to data Sequencer
            vscr.m_rq_mfb_data_sqr    = m_mfb_rq_env.m_sequencer.m_data;
            vscr.m_cc_mfb_data_sqr    = m_mfb_cc_env.m_sequencer.m_data;

            // Connect MFB environments to metadata Sequencer
            vscr.m_rq_mfb_meta_sqr    = m_mfb_rq_env.m_sequencer.m_meta;
            vscr.m_cc_mfb_meta_sqr    = m_mfb_cc_env.m_sequencer.m_meta;

            // Connect AXI environments to data Sequencer
            vscr.m_axi_cq_data_sqr    = m_axi_cq_env.m_sequencer.m_data;
            vscr.m_axi_rc_data_sqr    = m_axi_rc_env.m_sequencer.m_data;
            // Connect AXI environments to READY Sequencer
            vscr.m_axi_cc_rdy_sqr     = m_axi_cc_env.m_sequencer;
            vscr.m_axi_rq_rdy_sqr     = m_axi_rq_env.m_sequencer;
        end

        // Connect MFB environments to Scoreboard
        // RQ environment
        m_mfb_rq_env.analysis_port_data.connect(m_scoreboard.analysis_imp_mfb_rq_data);
        // RC environment
        m_mfb_rc_env.analysis_port_data.connect(m_scoreboard.analysis_imp_mfb_rc_data);
        // CQ environment
        m_mfb_cq_env.analysis_port_data.connect(m_scoreboard.analysis_imp_mfb_cq_data);
        // CC environment
        m_mfb_cc_env.analysis_port_data.connect(m_scoreboard.analysis_imp_mfb_cc_data);

        // ------------------------------------------------------------------
        // Reset sync connection
        // ------------------------------------------------------------------

        // Create AVALON environments to Reset agent sync
        m_reset.sync_connect(m_avst_down_env.reset_sync);
        m_reset.sync_connect(m_avst_up_env.reset_sync);
        // Create Credit Control agents Reset agent sync
        m_reset.sync_connect(m_crdt_agent_up.reset_sync);
        // m_reset.sync_connect(m_crdt_agent_down.reset_sync);
        // Create AXI environments to Reset agent sync
        m_reset.sync_connect(m_axi_cq_env.reset_sync);
        m_reset.sync_connect(m_axi_cc_env.reset_sync);
        m_reset.sync_connect(m_axi_rc_env.reset_sync);
        m_reset.sync_connect(m_axi_rq_env.reset_sync);
        // Create MFB environments to Reset agent sync
        m_reset.sync_connect(m_mfb_rq_env.reset_sync);
        m_reset.sync_connect(m_mfb_rc_env.reset_sync);
        m_reset.sync_connect(m_mfb_cq_env.reset_sync);
        m_reset.sync_connect(m_mfb_cc_env.reset_sync);

        // Connect MFB environments to DST RDY Sequencer
        vscr.m_mfb_rc_dst_rdy_sqr = m_mfb_rc_env.m_sequencer;
        vscr.m_mfb_cq_dst_rdy_sqr = m_mfb_cq_env.m_sequencer;
        // Connect Reset agent to Sequencer
        vscr.m_reset              = m_reset.m_sequencer;

    endfunction

    virtual task run_phase(uvm_phase phase);
        if(IS_INTEL_DEV) begin
            if (m_avst_down_cfg.active == UVM_ACTIVE && m_cc_mfb_cfg.active == UVM_ACTIVE && m_rq_mfb_cfg.active == UVM_ACTIVE) begin
                logic_vector_sequence #(AVST_DOWN_META_W)        logic_vector_seq_avst_down;
                logic_vector_sequence #(CC_MFB_META_W)           logic_vector_seq_cc;
                logic_vector_sequence #(RQ_MFB_META_W)           logic_vector_seq_rq;
                logic_vector_array_sequence #(CQ_MFB_ITEM_WIDTH) logic_vector_array_seq_avst_down;
                logic_vector_array_sequence #(CC_MFB_ITEM_WIDTH) logic_vector_array_seq_cc;
                logic_vector_array_sequence #(RQ_MFB_ITEM_WIDTH) logic_vector_array_seq_rq;

                logic_vector_seq_avst_down = logic_vector_sequence #(AVST_DOWN_META_W)::type_id::create("logic_vector_seq_avst_down", this);
                logic_vector_seq_cc        = logic_vector_sequence #(CC_MFB_META_W)::type_id::create("logic_vector_seq_cc", this);
                logic_vector_seq_rq        = logic_vector_sequence #(RQ_MFB_META_W)::type_id::create("logic_vector_seq_rq", this);

                logic_vector_seq_avst_down.tr_export = m_avst_down_generator.logic_vector_export;
                logic_vector_seq_cc.tr_export        = m_cc_generator.logic_vector_export;
                logic_vector_seq_rq.tr_export        = m_rq_generator.logic_vector_export;

                logic_vector_seq_avst_down.randomize();
                logic_vector_seq_cc.randomize();
                logic_vector_seq_rq.randomize();

                logic_vector_array_seq_avst_down = logic_vector_array_sequence#(CQ_MFB_ITEM_WIDTH)::type_id::create("logic_vector_array_seq_avst_down", this);
                logic_vector_array_seq_cc        = logic_vector_array_sequence#(CC_MFB_ITEM_WIDTH)::type_id::create("logic_vector_array_seq_cc", this);
                logic_vector_array_seq_rq        = logic_vector_array_sequence#(RQ_MFB_ITEM_WIDTH)::type_id::create("logic_vector_array_seq_rq", this);

                logic_vector_array_seq_avst_down.tr_export = m_avst_down_generator.logic_vector_array_export;
                logic_vector_array_seq_cc.tr_export        = m_cc_generator.logic_vector_array_export;
                logic_vector_array_seq_rq.tr_export        = m_rq_generator.logic_vector_array_export;

                logic_vector_array_seq_avst_down.randomize();
                logic_vector_array_seq_cc.randomize();
                logic_vector_array_seq_rq.randomize();

                fork
                    logic_vector_seq_avst_down.start(m_avst_down_env.m_sequencer.m_meta);
                    logic_vector_array_seq_avst_down.start(m_avst_down_env.m_sequencer.m_data);
                    logic_vector_seq_cc.start(m_mfb_cc_env.m_sequencer.m_meta);
                    logic_vector_array_seq_cc.start(m_mfb_cc_env.m_sequencer.m_data);
                    logic_vector_seq_rq.start(m_mfb_rq_env.m_sequencer.m_meta);
                    logic_vector_array_seq_rq.start(m_mfb_rq_env.m_sequencer.m_data);
                join_none
            end
        end
    endtask
endclass
