// env.sv: Verification environment
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Daniel Kriz <danielkriz@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

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

     int unsigned ITEM_WIDTH,
     int unsigned DMA_PORTS,
     int unsigned PCIE_ENDPOINTS,
     int unsigned PCIE_CONS,
     int unsigned DMA_BAR_ENABLE,
     string       PCIE_ENDPOINT_TYPE,
     string       DEVICE
) extends uvm_env;

    localparam STRADDLING = 0;
    `uvm_component_param_utils(uvm_pcie_top::env #(
            RQ_MFB_REGIONS, RQ_MFB_REGION_SIZE, RQ_MFB_BLOCK_SIZE,
            RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE,
            CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE,
            CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE,
            ITEM_WIDTH,  DMA_PORTS, PCIE_ENDPOINTS,  PCIE_CONS, DMA_BAR_ENABLE, PCIE_ENDPOINT_TYPE, DEVICE)
    );

    localparam TAG_WIDTH        = 8;
    localparam REQUEST_DEVICE   = 2;
    localparam BAR0_BASE_ADDR    = 32'h01000000;
    localparam BAR1_BASE_ADDR    = 32'h02000000;
    localparam BAR2_BASE_ADDR    = 32'h03000000;
    localparam BAR3_BASE_ADDR    = 32'h04000000;
    localparam BAR4_BASE_ADDR    = 32'h05000000;
    localparam BAR5_BASE_ADDR    = 32'h06000000;
    localparam EXP_ROM_BASE_ADDR = 32'h0A000000;
    // verilog_lint: waive line-length
    localparam uvm_pcie_mfb::device_t MFB_DEVICE = (DEVICE == "STRATIX10" || DEVICE == "AGILEX") ? uvm_pcie_mfb::DEV_INTEL : uvm_pcie_mfb::DEV_XILINX;

    uvm_pcie_top::sequencer#(RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE,
                             CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE,
                             ITEM_WIDTH, DMA_PORTS, PCIE_ENDPOINTS) m_sequencer;

    // PCIE
    uvm_pcie::dev  m_pcie_dev[PCIE_ENDPOINTS];
    uvm_pcie::root m_pcie_env[PCIE_ENDPOINTS];
    //uvm_pcie::env
    // DMA INTERFACE
    protected uvm_dma::env#(RQ_MFB_REGIONS, RQ_MFB_REGIONS, RQ_MFB_REGION_SIZE, RQ_MFB_BLOCK_SIZE, ITEM_WIDTH,
                  RC_MFB_REGIONS, RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, ITEM_WIDTH,
                  0 ) m_dma_env[PCIE_ENDPOINTS][DMA_PORTS];

    protected uvm_pcie::dev  m_dma_dev[PCIE_ENDPOINTS][DMA_PORTS]; //Register request and response
    protected uvm_pcie_mfb::env_tx #(
            CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, uvm_pcie_mfb::MFB_CQ,
            uvm_pcie_mfb::MFB_META_SOF, MFB_DEVICE
    ) m_cq_env[PCIE_ENDPOINTS][DMA_PORTS];
    protected uvm_pcie_mfb::env_rx #(
            CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, uvm_pcie_mfb::MFB_CC,
            uvm_pcie_mfb::MFB_META_SOF, STRADDLING, MFB_DEVICE
    ) m_cc_env[PCIE_ENDPOINTS][DMA_PORTS];

    //CONFIGURATION INTERFACE
    protected uvm_mi::agent_master #(32, 32) m_mi_agent[PCIE_ENDPOINTS];
    // Reset agent
    protected uvm_reset::agent                m_dma_reset;
    protected uvm_reset::agent                m_mi_reset;
    protected uvm_reset::env#(PCIE_CONS)      m_pcie_sysrst_n;
    protected uvm_reset::agent                m_pcie_reset[PCIE_ENDPOINTS];

    /*
    //NEW CONVERTORS
    */
    uvm_pcie_top::scoreboard #(
            CQ_MFB_REGIONS, PCIE_ENDPOINTS, DMA_PORTS, ITEM_WIDTH, DMA_BAR_ENABLE, PCIE_ENDPOINT_TYPE
    ) m_scoreboard;

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
            uvm_reset::config_item pcie_reset_cfg;
            uvm_mi::config_item m_mi_cfg;
            uvm_pcie::config_item m_pcie_cfg;
            string i_string;
            i_string.itoa(pcie);

            //PCIE EXPRESS
            m_pcie_cfg     = new();
            m_pcie_cfg.active         = UVM_ACTIVE;
            m_pcie_cfg.interface_name = {"vif_pcie_", i_string};
            uvm_config_db #(uvm_pcie::config_item)::set(this, {"m_pcie_", i_string}, "m_config", m_pcie_cfg);
            m_pcie_env[pcie] = uvm_pcie::root::type_id::create({"m_pcie_", i_string},this);
            m_pcie_dev[pcie] = uvm_pcie::dev::type_id::create({"m_pcie_", i_string, "_dev"}, this);

            // PCIE RESET
            pcie_reset_cfg                = new();
            pcie_reset_cfg.active         = UVM_PASSIVE;
            pcie_reset_cfg.interface_name = $sformatf("vif_pcie_user_reset_%0d", pcie);
            uvm_config_db #(uvm_reset::config_item)::set(this, {"m_pcie_reset_", i_string}, "m_config", pcie_reset_cfg);
            m_pcie_reset[pcie] = uvm_reset::agent::type_id::create({"m_pcie_reset_", i_string}, this);

            //MI INTERFACE(CQ + CC)
            m_mi_cfg                = new();
            m_mi_cfg.active         = UVM_ACTIVE;
            m_mi_cfg.interface_name = {"vif_mi_", i_string};
            uvm_config_db#(uvm_mi::config_item)::set(this, {"m_mi_agent_", i_string}, "m_config", m_mi_cfg);
            m_mi_agent[pcie] = uvm_mi::agent_master #(32, 32)::type_id::create({"m_mi_agent_", i_string}, this);

            for (int dma = 0; dma < DMA_PORTS; dma++) begin
                string dma_string = {i_string, $sformatf("_%0d", dma)};
                // MFB configuration
                uvm_dma::config_item m_dma_cfg;
                uvm_pcie::config_item m_pcie_cq_cfg;
                uvm_pcie::config_item m_pcie_cc_cfg;

                //RQ DMA
                m_dma_cfg = new();
                m_dma_cfg.interface_name = {"vif_dma_", dma_string};
                uvm_config_db #(uvm_dma::config_item)::set(this, {"m_dma_env_", dma_string}, "m_config", m_dma_cfg);
                m_dma_env[pcie][dma] = uvm_dma::env#(
                                            // verilog_lint: waive line-length
                                            RQ_MFB_REGIONS, RQ_MFB_REGIONS, RQ_MFB_REGION_SIZE, RQ_MFB_BLOCK_SIZE, ITEM_WIDTH,
                                            // verilog_lint: waive line-length
                                            RC_MFB_REGIONS, RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, ITEM_WIDTH,
                                            0 )::type_id::create({"m_dma_env_", dma_string}, this);


                m_dma_dev[pcie][dma] = uvm_pcie::dev::type_id::create({"m_dma_dev_", dma_string}, this);

                m_pcie_cq_cfg = new();
                m_pcie_cq_cfg.active         = UVM_ACTIVE;
                m_pcie_cq_cfg.interface_name = {"vif_dma_cq_", dma_string};
                uvm_config_db #(uvm_pcie::config_item)::set(
                    this,
                    {"m_cq_env_", dma_string},
                    "m_config",
                    m_pcie_cq_cfg
                );
                m_cq_env[pcie][dma] = uvm_pcie_mfb::env_tx #(
                                            CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE,
                                            uvm_pcie_mfb::MFB_CQ, uvm_pcie_mfb::MFB_META_SOF,
                                            MFB_DEVICE)::type_id::create({"m_cq_env_", dma_string}, this);

                m_pcie_cc_cfg = new();
                m_pcie_cc_cfg.active         = UVM_ACTIVE;
                m_pcie_cc_cfg.interface_name = {"vif_dma_cc_", dma_string};
                uvm_config_db #(uvm_pcie::config_item)::set(
                    this,
                    {"m_cc_env_", dma_string},
                    "m_config",
                    m_pcie_cc_cfg
                );
                m_cc_env[pcie][dma] = uvm_pcie_mfb::env_rx #(
                                            CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE,
                                            uvm_pcie_mfb::MFB_CC, uvm_pcie_mfb::MFB_META_SOF,
                                            STRADDLING, MFB_DEVICE)::type_id::create({"m_cc_env_", dma_string}, this);
            end
        end

        //RESET INTERFACE
        uvm_config_db #(uvm_reset::env_config_item #(PCIE_CONS))::set(this, "m_pcie_sysrst_n", "m_config",
                                                                    m_pcie_sysrst_n_cfg);
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

        m_scoreboard = uvm_pcie_top::scoreboard#(
                            CQ_MFB_REGIONS, PCIE_ENDPOINTS, DMA_PORTS, ITEM_WIDTH,
                            DMA_BAR_ENABLE, PCIE_ENDPOINT_TYPE)::type_id::create("m_scoreboard", this);
        m_sequencer  = uvm_pcie_top::sequencer#(
                            RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE,
                            CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE,
                            ITEM_WIDTH, DMA_PORTS, PCIE_ENDPOINTS)::type_id::create("m_sequencer",this);
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);
        uvm_pcie::bar_config bar_cfg = new();

        bar_cfg.register(0, BAR0_BASE_ADDR[32-1:2]);
        bar_cfg.register(1, BAR1_BASE_ADDR[32-1:2]);
        bar_cfg.register(2, BAR2_BASE_ADDR[32-1:2]);
        bar_cfg.register(3, BAR3_BASE_ADDR[32-1:2]);
        bar_cfg.register(4, BAR4_BASE_ADDR[32-1:2]);
        bar_cfg.register(5, BAR5_BASE_ADDR[32-1:2]);
        bar_cfg.register(6, EXP_ROM_BASE_ADDR[32-1:2]);


        for (int unsigned pcie = 0; pcie < PCIE_ENDPOINTS; pcie++) begin

            // SET BAR
            m_pcie_env[pcie].bar_register(bar_cfg);

            //PCIE CONNECT
            m_pcie_env[pcie].analysis_port_rc.connect(m_scoreboard.pcie_rc[pcie]);
            m_pcie_env[pcie].analysis_port_cq.connect(m_scoreboard.pcie_cq[pcie]);
            m_pcie_env[pcie].analysis_port_rq.connect(m_scoreboard.pcie_rq[pcie]);
            m_pcie_env[pcie].analysis_port_cc.connect(m_scoreboard.pcie_cc[pcie]);

            m_pcie_env[pcie].analysis_port_rq.connect(m_pcie_dev[pcie].port_pcie);
            m_pcie_env[pcie].analysis_port_cc.connect(m_pcie_dev[pcie].port_pcie);
            uvm_config_db#(uvm_pcie::pcie_info#(TAG_WIDTH))::set(
                m_pcie_env[pcie].m_sequencer_cq,
                "",
                "pcie_info",
                m_pcie_dev[pcie].tx_info
            );
            uvm_config_db#(uvm_pcie::pcie_info#(TAG_WIDTH))::set(
                m_pcie_env[pcie].m_sequencer_rc,
                "",
                "pcie_info",
                m_pcie_dev[pcie].rx_info
            );

            //MI CONNECT
            m_mi_agent[pcie].analysis_port_rq.connect(m_scoreboard.mi_req[pcie]);
            m_mi_agent[pcie].analysis_port_rs.connect(m_scoreboard.mi_rsp[pcie]);

            m_sequencer.m_mi_sqr[pcie]  = m_mi_agent[pcie].m_sequencer;
            m_sequencer.m_pcie_cq[pcie] = m_pcie_env[pcie].m_sequencer_cq;
            m_sequencer.m_pcie_rc[pcie] = m_pcie_env[pcie].m_sequencer_rc;
            m_pcie_reset[pcie].sync_connect(m_pcie_env[pcie].reset_sync);

            for (int unsigned  dma = 0; dma < DMA_PORTS; dma++) begin
                m_cq_env[pcie][dma].bar_register(bar_cfg);
                m_cc_env[pcie][dma].bar_register(bar_cfg);

                m_dma_env[pcie][dma].rc_analysis_port.connect(m_scoreboard.dma_rc[pcie][dma]);
                m_dma_env[pcie][dma].rq_analysis_port.connect(m_scoreboard.dma_rq[pcie][dma]);

                m_cq_env[pcie][dma].analysis_port.connect(m_scoreboard.dma_cq[pcie][dma]);
                m_cc_env[pcie][dma].analysis_port.connect(m_scoreboard.dma_cc[pcie][dma]);
                m_cq_env[pcie][dma].analysis_port.connect(m_dma_dev[pcie][dma].port_pcie);
                uvm_config_db#(uvm_pcie::pcie_info#(TAG_WIDTH))::set(
                    m_cc_env[pcie][dma].m_sequencer,
                    "",
                    "pcie_info",
                    m_dma_dev[pcie][dma].tx_info
                );

                // ------------------------------------------------------------------
                // Reset sync connection
                // ------------------------------------------------------------------
                m_dma_reset.sync_connect(m_dma_env[pcie][dma].reset_sync);

                m_dma_reset.sync_connect(m_cq_env[pcie][dma].reset_sync);
                m_dma_reset.sync_connect(m_cc_env[pcie][dma].reset_sync);

                //SEQUENCER
                m_sequencer.m_dma_rq[pcie][dma]     = m_dma_env[pcie][dma].m_sequencer;
                m_sequencer.m_dma_cc[pcie][dma]     = m_cc_env[pcie][dma].m_sequencer;
            end
        end

        //
        m_scoreboard. model_config(bar_cfg);

        // Connect Reset agent to Sequencer
        m_sequencer.m_dma_reset     = m_dma_reset.m_sequencer;
        m_sequencer.m_mi_reset      = m_mi_reset.m_sequencer;
        m_sequencer.m_pcie_sysrst_n = m_pcie_sysrst_n.m_sequencer;
    endfunction
endclass
