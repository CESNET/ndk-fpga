//-- env.sv: Verification environment
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// Environment for functional verification of encode.
// This environment containts two mii agents.
class env #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, META_WIDTH, READY_LATENCY) extends uvm_env;

    `uvm_component_param_utils(uvm_pcie_avst2mfb::env #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, META_WIDTH, READY_LATENCY));

    uvm_logic_vector_array_mfb::env_tx #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, META_WIDTH)  mfb_tx_env;
    uvm_logic_vector_array_mfb::config_item                                                                         mfb_tx_cfg;
    uvm_logic_vector_array_avst::env_rx #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, META_WIDTH, READY_LATENCY) avst_env;
    uvm_logic_vector_array_avst::config_item                                                                        avst_cfg;

    uvm_pcie_avst2mfb::virt_sequencer#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, META_WIDTH) vscr;
    uvm_reset::agent                                                                                             m_reset;
    uvm_reset::config_item                                                                                       m_config_reset;

    scoreboard #(MFB_ITEM_WIDTH, META_WIDTH) m_scoreboard;


    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);

        avst_cfg   = new;
        mfb_tx_cfg = new;

        avst_cfg.active   = UVM_ACTIVE;
        mfb_tx_cfg.active = UVM_ACTIVE;

        avst_cfg.interface_name   = "vif_tx";
        mfb_tx_cfg.interface_name = "vif_rx";

        avst_cfg.meta_behav   = uvm_logic_vector_array_avst::config_item::META_SOF;
        mfb_tx_cfg.meta_behav = uvm_logic_vector_array_mfb::config_item::META_SOF;

        mfb_tx_cfg.seq_type = "PCIE";
        mfb_tx_cfg.seq_cfg  = new();
        mfb_tx_cfg.seq_cfg.straddling_set(0);
        avst_cfg.seq_cfg = new();
        avst_cfg.seq_cfg.straddling_set(0);

        m_config_reset                = new;
        m_config_reset.active         = UVM_ACTIVE;
        m_config_reset.interface_name = "vif_reset";

        uvm_config_db #(uvm_reset::config_item)::set(this, "m_reset", "m_config", m_config_reset);
        m_reset = uvm_reset::agent::type_id::create("m_reset", this);

        uvm_config_db #(uvm_logic_vector_array_avst::config_item)::set(this, "avst_env", "m_config", avst_cfg);
        uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, "mfb_tx_env", "m_config", mfb_tx_cfg);

        avst_env  = uvm_logic_vector_array_avst::env_rx #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, META_WIDTH, READY_LATENCY)::type_id::create("avst_env", this);
        mfb_tx_env    = uvm_logic_vector_array_mfb::env_tx #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, META_WIDTH)::type_id::create("mfb_tx_env", this);

        m_scoreboard = scoreboard #(MFB_ITEM_WIDTH, META_WIDTH)::type_id::create("m_scoreboard", this);
        vscr         = uvm_pcie_avst2mfb::virt_sequencer#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, META_WIDTH)::type_id::create("vscr",this);
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);

        mfb_tx_env.analysis_port_data.connect(m_scoreboard.analysis_imp_mfb_data);
        mfb_tx_env.analysis_port_meta.connect(m_scoreboard.analysis_imp_mfb_meta);
        avst_env.analysis_port_data.connect(m_scoreboard.analysis_imp_avst_data);
        avst_env.analysis_port_meta.connect(m_scoreboard.analysis_imp_avst_meta);

        m_reset.sync_connect(mfb_tx_env.reset_sync);
        m_reset.sync_connect(avst_env.reset_sync);

        vscr.m_reset                  = m_reset.m_sequencer;
        vscr.m_logic_vector_array_scr = avst_env.m_sequencer.m_data;
        vscr.m_logic_vector_scr       = avst_env.m_sequencer.m_meta;
        vscr.m_pcie                   = mfb_tx_env.m_sequencer;

    endfunction
endclass
