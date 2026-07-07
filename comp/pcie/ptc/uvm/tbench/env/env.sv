//-- env.sv: Verification environment
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


class env#(
    int unsigned MVB_UP_ITEMS,
    int unsigned RQ_MVB_ITEMS,
    int unsigned RQ_MFB_REGIONS,
    int unsigned RQ_MFB_REGION_SIZE,
    int unsigned RQ_MFB_BLOCK_SIZE,

    int unsigned RC_MVB_ITEMS,
    int unsigned RC_MFB_REGIONS,
    int unsigned RC_MFB_REGION_SIZE,
    int unsigned RC_MFB_BLOCK_SIZE,

    int unsigned DMA_PORTS,
    int unsigned PCIE_TAG_WIDTH,
    logic        PTC_DISABLED
) extends uvm_env;
    `uvm_component_param_utils(uvm_ptc::env#(MVB_UP_ITEMS,
                                             RQ_MVB_ITEMS, RQ_MFB_REGIONS, RQ_MFB_REGION_SIZE, RQ_MFB_BLOCK_SIZE,
                                             RC_MVB_ITEMS, RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE,
                                             DMA_PORTS, PCIE_TAG_WIDTH, PTC_DISABLED)
                              );

    sequencer#(DMA_PORTS) m_sequencer;

    // RESET
    protected uvm_reset::agent  m_dma_reset;
    protected uvm_reset::agent  m_reset;

    // DMA SIDE
    protected uvm_dma::env#(RQ_MVB_ITEMS, RQ_MFB_REGIONS, RQ_MFB_REGION_SIZE, RQ_MFB_BLOCK_SIZE, 32,
                  RC_MVB_ITEMS, RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, 32,
                  PTC_DISABLED
                 ) m_dma[DMA_PORTS];

    //PCIE side
    uvm_pcie::dev m_pcie_dev;
    protected uvm_pcie::env_tx m_pcie_rq;
    protected uvm_pcie::env_rx m_pcie_rc;

    //SCOREBOARD AND MODEL
    protected model#(MVB_UP_ITEMS, DMA_PORTS) m_model;
    protected scoreboard#(DMA_PORTS)          m_scoreboard;


    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= m_model.used();
        ret |= m_scoreboard.used();
        return ret;
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);
        uvm_pcie::config_item pcie_rq_cfg;
        uvm_pcie::config_item pcie_rc_cfg;
        model_ptc_config ptc_cfg;
        uvm_reset::config_item  m_reset_dma_cfg;
        uvm_reset::config_item  m_reset_cfg;


        pcie_rq_cfg = new();
        pcie_rq_cfg.active = UVM_ACTIVE;
        pcie_rq_cfg.interface_name = "vif_pcie_rq";
        uvm_config_db #(uvm_pcie::config_item)::set(this, "m_pcie_rq", "m_config", pcie_rq_cfg);
        m_pcie_rq = uvm_pcie::env_tx::type_id::create("m_pcie_rq", this);

        pcie_rc_cfg = new();
        pcie_rc_cfg.active = UVM_ACTIVE;
        pcie_rc_cfg.interface_name = "vif_pcie_rc";
        uvm_config_db #(uvm_pcie::config_item)::set(this, "m_pcie_rc", "m_config", pcie_rc_cfg);
        m_pcie_rc = uvm_pcie::env_rx::type_id::create("m_pcie_rc", this);
        // DEVICE
        m_pcie_dev = uvm_pcie::dev::type_id::create("m_pcie_dev", this);

        for (int unsigned it = 0; it < DMA_PORTS; it++) begin
            uvm_dma::config_item dma_cfg;
            const string dma_name = $sformatf("m_dma_%0d", it);

            dma_cfg = new();
            dma_cfg.interface_name = $sformatf("vif_dma_%0d", it);
            uvm_config_db #(uvm_dma::config_item)::set(this, dma_name, "m_config", dma_cfg);
            m_dma[it] =  uvm_dma::env#(RQ_MVB_ITEMS, RQ_MFB_REGIONS, RQ_MFB_REGION_SIZE, RQ_MFB_BLOCK_SIZE, 32,
                                       RC_MVB_ITEMS, RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, 32,
                                       PTC_DISABLED
                                      )::type_id::create(dma_name, this);
        end

        // RESET
        m_reset_dma_cfg                = new();
        m_reset_dma_cfg.active         = UVM_ACTIVE;
        m_reset_dma_cfg.interface_name = "vif_reset_dma";
        uvm_config_db #(uvm_reset::config_item)::set(this, "m_dma_reset", "m_config", m_reset_dma_cfg);
        m_dma_reset  = uvm_reset::agent::type_id::create("m_dma_reset", this);

        m_reset_cfg                = new();
        m_reset_cfg.active         = UVM_ACTIVE;
        m_reset_cfg.interface_name = "vif_reset";
        uvm_config_db #(uvm_reset::config_item)::set(this, "m_reset", "m_config", m_reset_cfg);
        m_reset  = uvm_reset::agent::type_id::create("m_reset", this);

        m_sequencer = sequencer#(DMA_PORTS)::type_id::create("m_sequencer", this);

        ptc_cfg = new();
        ptc_cfg.path = "testbench.DUT_U.VHDL_DUT_U.ptc_i";
        uvm_config_db #(model_ptc_config)::set(this, "m_model", "m_config", ptc_cfg);
        m_model = model#(MVB_UP_ITEMS, DMA_PORTS)::type_id::create("m_model", this);

        m_scoreboard = scoreboard#(DMA_PORTS)::type_id::create("m_scoreboard"     , this);
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);
        for (int unsigned it = 0; it < DMA_PORTS; it++) begin
            m_dma[it].rq_analysis_port.connect(m_model.dma_rq[it].analysis_export);
            m_dma[it].rc_analysis_port.connect(m_scoreboard.dma_rc_cmp[it].analysis_imp_dut);
            m_model.dma_rc[it].connect(m_scoreboard.dma_rc_cmp[it].analysis_imp_model);

            m_sequencer.m_dma[it] = m_dma[it].m_sequencer;

            m_dma_reset.sync_connect(m_dma[it].reset_sync);
        end

        m_pcie_rc.analysis_port.connect(m_model.pcie_rc.analysis_export);
        m_pcie_rq.analysis_port.connect(m_scoreboard.pcie_rq_cmp.analysis_imp_dut);
        m_pcie_rq.analysis_port.connect(m_pcie_dev.port_pcie);
        uvm_config_db #(uvm_pcie::pcie_info #(PCIE_TAG_WIDTH))::set(m_pcie_rc.m_sequencer, "", "pcie_info",
                                                                  m_pcie_dev.rx_info);
        m_model.pcie_rq.connect(m_scoreboard.pcie_rq_cmp.analysis_imp_model);

        m_sequencer.m_dma_reset = m_dma_reset.m_sequencer;
        m_sequencer.m_reset     = m_reset.m_sequencer;
        m_sequencer.m_pcie_rc   = m_pcie_rc.m_sequencer;

        m_reset.sync_connect(m_pcie_rq.reset_sync);
        m_reset.sync_connect(m_pcie_rc.reset_sync);
    endfunction

endclass
