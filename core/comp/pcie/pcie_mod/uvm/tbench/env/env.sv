// env.sv: Verification environment
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Daniel Kriz <danielkriz@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class env #(
     RQ_MFB_REGIONS,
     RQ_MFB_REGION_SIZE,
     RQ_MFB_BLOCK_SIZE,
     RQ_MFB_META_W,

     RC_MFB_REGIONS,
     RC_MFB_REGION_SIZE,
     RC_MFB_BLOCK_SIZE,
     RC_MFB_META_W,

     CQ_MFB_REGIONS,
     CQ_MFB_REGION_SIZE,
     CQ_MFB_BLOCK_SIZE,
     CQ_MFB_META_W,

     CC_MFB_REGIONS,
     CC_MFB_REGION_SIZE,
     CC_MFB_BLOCK_SIZE,
     CC_MFB_META_W,

     ITEM_WIDTH,
     DMA_PORTS,
     PCIE_ENDPOINTS,
     PCIE_CONS,
     DEVICE
) extends uvm_env;

    `uvm_component_param_utils(uvm_pcie_top::env #(RQ_MFB_REGIONS, RQ_MFB_REGION_SIZE, RQ_MFB_BLOCK_SIZE, RQ_MFB_META_W,
                                                   RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, RC_MFB_META_W,
                                                   CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, CQ_MFB_META_W,
                                                   CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, CC_MFB_META_W,
                                                   ITEM_WIDTH,  DMA_PORTS, PCIE_ENDPOINTS,  PCIE_CONS, DEVICE));

    localparam REQUEST_DEVICE = 2;

    localparam IS_INTEL_DEV = (DEVICE == "STRATIX10" || DEVICE == "AGILEX");
    uvm_pcie_top::sequencer#(RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, RC_MFB_META_W,
                             CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, CQ_MFB_META_W,
                             ITEM_WIDTH, RQ_MFB_META_W, CC_MFB_META_W, DMA_PORTS, PCIE_ENDPOINTS) m_sequencer;

    // PCIE
    uvm_pcie::env m_pcie_env[PCIE_ENDPOINTS];
    // DMA INTERFACE
    uvm_dma::env#(RQ_MFB_REGIONS, RQ_MFB_REGION_SIZE, RQ_MFB_BLOCK_SIZE, ITEM_WIDTH, RQ_MFB_META_W,
                  RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, ITEM_WIDTH, RC_MFB_META_W) m_dma_env[PCIE_ENDPOINTS][DMA_PORTS];

    protected uvm_logic_vector_array_mfb::env_tx #(CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, ITEM_WIDTH, CQ_MFB_META_W) m_mfb_cq_env[PCIE_ENDPOINTS][DMA_PORTS];
    protected uvm_logic_vector_array_mfb::env_rx #(CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, ITEM_WIDTH, CC_MFB_META_W) m_mfb_cc_env[PCIE_ENDPOINTS][DMA_PORTS];
    //CONFIGURATION INTERFACE
    protected uvm_mi::agent_master #(32, 32) m_mi_agent[PCIE_ENDPOINTS];
    // Reset agent
    protected uvm_reset::agent                m_dma_reset;
    protected uvm_reset::agent                m_mi_reset;
    protected uvm_reset::env#(PCIE_CONS)      m_pcie_sysrst_n;

    /*
    //NEW CONVERTORS
    */
    uvm_pcie_top::scoreboard #(CQ_MFB_REGIONS, PCIE_ENDPOINTS, DMA_PORTS, ITEM_WIDTH) m_scoreboard;

    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);
        uvm_reset::config_item                   m_dma_reset_cfg;
        uvm_reset::config_item                   m_mi_reset_cfg;
        uvm_reset::env_config_item #(PCIE_CONS)  m_pcie_sysrst_n_cfg;

        m_pcie_sysrst_n_cfg = new();
        m_pcie_sysrst_n_cfg.driver_delay = 40ns;

        for(int unsigned pcie_con = 0; pcie_con < PCIE_CONS; pcie_con++) begin
            //SETUP RESET
            m_pcie_sysrst_n_cfg.active[pcie_con]         = UVM_ACTIVE;
            m_pcie_sysrst_n_cfg.interface_name[pcie_con] = $sformatf("vif_pcie_sysrst_n_%0d", pcie_con);
        end

        for(int unsigned pcie = 0; pcie < PCIE_ENDPOINTS; pcie++) begin
            uvm_mi::config_item m_mi_cfg;
            uvm_pcie::config_item m_pcie_cfg;
            uvm_dma::config_item m_dma_cfg;
            string i_string;
            i_string.itoa(pcie);

            //PCIE EXPRESS
            m_pcie_cfg     = new();
            m_pcie_cfg.active         = UVM_ACTIVE;
            m_pcie_cfg.interface_name = {"vif_pcie_", i_string};
            uvm_config_db #(uvm_pcie::config_item)::set(this, {"m_pcie_", i_string}, "m_config", m_pcie_cfg);
            m_pcie_env[pcie] = uvm_pcie::env::type_id::create({"m_pcie_", i_string},this);

            //MI INTERFACE(CQ + CC)
            m_mi_cfg                = new();
            m_mi_cfg.active         = UVM_ACTIVE;
            m_mi_cfg.interface_name = {"vif_mi_", i_string};
            uvm_config_db#(uvm_mi::config_item)::set(this, {"m_mi_agent_", i_string}, "m_config", m_mi_cfg);
            m_mi_agent[pcie] = uvm_mi::agent_master #(32, 32)::type_id::create({"m_mi_agent_", i_string}, this);

            for (int dma = 0; dma < DMA_PORTS; dma++) begin
                string dma_string = {i_string, $sformatf("_%0d", dma)};
                // MFB configuration
                uvm_logic_vector_array_mfb::config_item  m_cq_mfb_cfg;
                uvm_logic_vector_array_mfb::config_item  m_cc_mfb_cfg;
                uvm_logic_vector_array_mfb::config_item  m_rc_mfb_cfg;
                uvm_logic_vector_mvb::config_item        m_rc_mvb_cfg;

                //RQ DMA
                m_dma_cfg = new();
                m_dma_cfg.interface_name_rq_mfb = {"vif_rq_mfb_", dma_string};
                m_dma_cfg.interface_name_rq_mvb = {"vif_rq_mvb_", dma_string};
                m_dma_cfg.interface_name_rc_mfb = {"vif_rc_mfb_", dma_string};
                m_dma_cfg.interface_name_rc_mvb = {"vif_rc_mvb_", dma_string};
                uvm_config_db #(uvm_dma::config_item)::set(this, {"m_dma_env_", dma_string}, "m_config", m_dma_cfg);
                m_dma_env[pcie][dma] = uvm_dma::env#(RQ_MFB_REGIONS, RQ_MFB_REGION_SIZE, RQ_MFB_BLOCK_SIZE, ITEM_WIDTH, RQ_MFB_META_W,
                  RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, ITEM_WIDTH, RC_MFB_META_W)::type_id::create({"m_dma_env_", dma_string}, this);

                //CQ
                m_cq_mfb_cfg = new();
                m_cq_mfb_cfg.active = UVM_ACTIVE;
                m_cq_mfb_cfg.interface_name    = {"vif_cq_mfb_", dma_string};
                m_cq_mfb_cfg.meta_behav = (IS_INTEL_DEV) ? uvm_logic_vector_array_mfb::config_item::META_SOF : uvm_logic_vector_array_mfb::config_item::META_NONE;
                m_cq_mfb_cfg.seq_type = "PCIE";
                m_cq_mfb_cfg.seq_cfg  = new();
                m_cq_mfb_cfg.seq_cfg.straddling_set(1);
                uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, {"m_mfb_cq_env_", dma_string}, "m_config", m_cq_mfb_cfg);
                m_mfb_cq_env[pcie][dma]    = uvm_logic_vector_array_mfb::env_tx #(CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, ITEM_WIDTH, CQ_MFB_META_W)::type_id::create({"m_mfb_cq_env_", dma_string}, this);

                //CC
                m_cc_mfb_cfg = new();
                m_cc_mfb_cfg.active = UVM_ACTIVE;
                m_cc_mfb_cfg.interface_name    = {"vif_cc_mfb_", dma_string};
                m_cc_mfb_cfg.meta_behav = (IS_INTEL_DEV) ? uvm_logic_vector_array_mfb::config_item::META_SOF : uvm_logic_vector_array_mfb::config_item::META_NONE;
                m_cc_mfb_cfg.seq_type = "PCIE";
                m_cc_mfb_cfg.seq_cfg  = new();
                m_cc_mfb_cfg.seq_cfg.straddling_set(1);
                uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, {"m_mfb_cc_env_", dma_string}, "m_config", m_cc_mfb_cfg);
                m_mfb_cc_env[pcie][dma] = uvm_logic_vector_array_mfb::env_rx #(CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, ITEM_WIDTH, CC_MFB_META_W)::type_id::create({"m_mfb_cc_env_", dma_string}, this);
            end
        end

        //RESET INTERFACE
        uvm_config_db#(uvm_reset::env_config_item#(PCIE_CONS))::set(this, "m_pcie_sysrst_n", "m_config", m_pcie_sysrst_n_cfg);
        m_pcie_sysrst_n = uvm_reset::env#(PCIE_CONS)::type_id::create("m_pcie_sysrst_n", this);

        // DMA Reset
        m_dma_reset_cfg                = new();
        m_mi_reset_cfg                 = new();
        m_dma_reset_cfg.active         = UVM_ACTIVE;
        m_mi_reset_cfg.active          = UVM_ACTIVE;
        m_dma_reset_cfg.interface_name = "vif_dma_reset";
        m_mi_reset_cfg.interface_name  = "vif_mi_reset";
        uvm_config_db #(uvm_reset::config_item)::set(this, "m_dma_reset", "m_config", m_dma_reset_cfg);
        uvm_config_db #(uvm_reset::config_item)::set(this, "m_mi_reset", "m_config", m_mi_reset_cfg);
        m_dma_reset = uvm_reset::agent::type_id::create("m_dma_reset", this);
        m_mi_reset  = uvm_reset::agent::type_id::create("m_mi_reset", this);

        m_scoreboard = uvm_pcie_top::scoreboard#(CQ_MFB_REGIONS, PCIE_ENDPOINTS, DMA_PORTS, ITEM_WIDTH)::type_id::create("m_scoreboard", this);
        m_sequencer  = uvm_pcie_top::sequencer#(RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, RC_MFB_META_W,
                                                CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, CQ_MFB_META_W,
                                                ITEM_WIDTH, RQ_MFB_META_W, CC_MFB_META_W, DMA_PORTS, PCIE_ENDPOINTS)::type_id::create("m_sequencer",this);
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);
        for (int unsigned cons = 0; cons < PCIE_CONS; cons++) begin
            for (int unsigned pcie_logic = 0; pcie_logic < PCIE_ENDPOINTS/PCIE_CONS; pcie_logic++) begin
                const int unsigned pcie = cons*PCIE_ENDPOINTS/PCIE_CONS + pcie_logic; 
                //PCIE CONNECT
                m_pcie_env[pcie].rc_analysis_port.connect(m_scoreboard.pcie_rc[pcie]);
                m_pcie_env[pcie].cq_analysis_port.connect(m_scoreboard.pcie_cq[pcie]);
                m_pcie_env[pcie].rq_analysis_port.connect(m_scoreboard.pcie_rq[pcie]);
                m_pcie_env[pcie].cc_analysis_port.connect(m_scoreboard.pcie_cc[pcie]);

                //MI CONNECT
                m_mi_agent[pcie].analysis_port_rq.connect(m_scoreboard.mi_req[pcie].analysis_export);
                m_mi_agent[pcie].analysis_port_rs.connect(m_scoreboard.mi_rsp[pcie]);

                m_sequencer.m_mi_sqr[pcie] = m_mi_agent[pcie].m_sequencer;
                m_sequencer.m_pcie[pcie]   = m_pcie_env[pcie].m_sequencer;
                m_pcie_sysrst_n.m_agent[cons].sync_connect(m_pcie_env[pcie].reset_sync);

                for (int dma = 0; dma < DMA_PORTS; dma++) begin
                    m_dma_env[pcie][dma].rc_analysis_port.connect(m_scoreboard.dma_rc[pcie][dma]);
                    m_dma_env[pcie][dma].rq_analysis_port.connect(m_scoreboard.dma_rq[pcie][dma]);

                    // ------------------------------------------------------------------
                    // Reset sync connection
                    // ------------------------------------------------------------------
                    m_dma_reset.sync_connect(m_dma_env[pcie][dma].reset_sync);

                    m_dma_reset.sync_connect(m_mfb_cq_env[pcie][dma].reset_sync);
                    m_dma_reset.sync_connect(m_mfb_cc_env[pcie][dma].reset_sync);

                    //SEQUENCER
                    m_sequencer.m_dma_rq[pcie][dma]          = m_dma_env[pcie][dma].m_sequencer;
                    m_sequencer.m_dma_rc_mfb[pcie][dma]      = m_dma_env[pcie][dma].m_rc_mfb_env.m_sequencer;
                    m_sequencer.m_dma_rc_mvb[pcie][dma]      = m_dma_env[pcie][dma].m_rc_mvb_env.m_sequencer;
                    m_sequencer.m_dma_cq[pcie][dma]          = m_mfb_cq_env[pcie][dma].m_sequencer;
                    m_sequencer.m_dma_cc_meta[pcie][dma]     = m_mfb_cc_env[pcie][dma].m_sequencer.m_meta;
                    m_sequencer.m_dma_cc_data[pcie][dma]     = m_mfb_cc_env[pcie][dma].m_sequencer.m_data;
                end
            end
        end

        // Connect Reset agent to Sequencer
        m_sequencer.m_dma_reset     = m_dma_reset.m_sequencer;
        m_sequencer.m_mi_reset      = m_mi_reset.m_sequencer;
        m_sequencer.m_pcie_sysrst_n = m_pcie_sysrst_n.m_sequencer;
    endfunction
endclass
