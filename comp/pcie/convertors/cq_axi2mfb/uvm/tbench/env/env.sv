//-- env.sv: Verification environment
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class env #(
    int unsigned MFB_REGIONS,
    int unsigned MFB_REGION_SIZE,
    int unsigned MFB_BLOCK_SIZE,
    logic STRADDLING,
    string DEVICE
) extends uvm_env;
    `uvm_component_param_utils(uvm_cq_mfb2axi::env #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, STRADDLING, DEVICE));

    localparam int unsigned MFB_ITEM_WIDTH = 32;
    localparam int unsigned AXI_ITEMS = MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE;

    uvm_cq_mfb2axi::sequencer m_sequencer;

    protected uvm_pcie_axi::env_rx#(AXI_ITEMS, uvm_pcie_axi::AXI_CQ, DEVICE, STRADDLING) axi_cq;
    protected uvm_logic_vector_array_mfb::env_tx #(
        MFB_REGIONS,
        MFB_REGION_SIZE,
        MFB_BLOCK_SIZE,
        MFB_ITEM_WIDTH,
        0
    ) mfb_cq_env;
    protected uvm_reset::agent                                                           m_reset;

    protected scoreboard m_scoreboard;

    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function int unsigned used();
        return m_scoreboard.used();
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);
        uvm_logic_vector_array_mfb::config_item  mfb_cq_cfg;
        uvm_reset::config_item                   m_config_reset;
        uvm_pcie::config_item                    pcie_cfg;

        pcie_cfg = new;
        pcie_cfg.active = UVM_ACTIVE;
        pcie_cfg.interface_name = "vif_rx";
        uvm_config_db #(uvm_pcie::config_item)::set(this, "axi_cq", "m_config", pcie_cfg);
        axi_cq = uvm_pcie_axi::env_rx #(
            AXI_ITEMS,
            uvm_pcie_axi::AXI_CQ,
            DEVICE,
            STRADDLING
        )::type_id::create("axi_cq", this);

        mfb_cq_cfg = new;
        mfb_cq_cfg.active = UVM_ACTIVE;
        mfb_cq_cfg.interface_name = "vif_tx";
        uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, "mfb_cq_env", "m_config", mfb_cq_cfg);
        mfb_cq_env = uvm_logic_vector_array_mfb::env_tx #(
            MFB_REGIONS,
            MFB_REGION_SIZE,
            MFB_BLOCK_SIZE,
            MFB_ITEM_WIDTH,
            0
        )::type_id::create("mfb_cq_env", this);

        m_config_reset                = new;
        m_config_reset.active         = UVM_ACTIVE;
        m_config_reset.interface_name = "vif_reset";
        uvm_config_db #(uvm_reset::config_item)::set(this, "m_reset", "m_config", m_config_reset);
        m_reset = uvm_reset::agent::type_id::create("m_reset", this);

        m_scoreboard = scoreboard::type_id::create("m_scoreboard", this);
        m_sequencer  = uvm_cq_mfb2axi::sequencer::type_id::create("m_sequencer",this);
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);

        mfb_cq_env.analysis_port_data.connect(m_scoreboard.cmp_data.analysis_imp_dut);
        //mfb_cq_env.analysis_port_meta.connect(m_scoreboard.cmp_tlp.analysis_imp_dut);
        axi_cq.analysis_port.connect(m_scoreboard.cmp_data.analysis_imp_model);
        //axi_cq.analysis_port.connect(m_scoreboard.cmp_tlp.analysis_imp_model);

        m_reset.sync_connect(mfb_cq_env.reset_sync);
        m_reset.sync_connect(axi_cq.reset_sync);

        m_sequencer.m_reset = m_reset.m_sequencer;
        m_sequencer.m_cq    = axi_cq.m_sequencer;
    endfunction
endclass
