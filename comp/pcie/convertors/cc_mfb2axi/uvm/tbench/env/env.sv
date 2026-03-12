//-- env.sv: Verification environment
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// Environment for functional verification of encode.
// This environment containts two mii agents.
class env #(
    int unsigned MFB_REGIONS,
    int unsigned MFB_REGION_SIZE,
    int unsigned MFB_BLOCK_SIZE,
    string DEVICE,
    logic STRADDLING
) extends uvm_env;

    `uvm_component_param_utils(uvm_pcie_cc_mfb2axi::env #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, DEVICE, STRADDLING));

    localparam ITEM_WIDTH = 32;
    localparam PCIE_ITEMS = MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE;

    uvm_logic_vector_array_mfb::env_rx #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, ITEM_WIDTH, 0) mfb_cc_env;
    uvm_pcie_axi::env_tx #(PCIE_ITEMS, uvm_pcie_axi::AXI_CC, DEVICE, STRADDLING)                      axi_cc_env;

    uvm_pcie_cc_mfb2axi::virt_sequencer vscr;
    uvm_reset::agent       m_reset;
    uvm_reset::config_item m_config_reset;

    scoreboard m_scoreboard;


    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);
        uvm_logic_vector_array_mfb::config_item mfb_cc_cfg;
        uvm_pcie::config_item axi_cc_cfg;

        axi_cc_cfg     = new;
        mfb_cc_cfg     = new;

        axi_cc_cfg.active = UVM_ACTIVE;
        mfb_cc_cfg.active = UVM_ACTIVE;

        axi_cc_cfg.interface_name = "vif_rx";
        mfb_cc_cfg.interface_name = "vif_tx";
        mfb_cc_cfg.set_pcie(STRADDLING);

        m_config_reset                = new;
        m_config_reset.active         = UVM_ACTIVE;
        m_config_reset.interface_name = "vif_reset";

        uvm_config_db #(uvm_reset::config_item)::set(this, "m_reset", "m_config", m_config_reset);
        m_reset = uvm_reset::agent::type_id::create("m_reset", this);

        uvm_config_db #(uvm_pcie::config_item)::set(this, "axi_cc_env", "m_config", axi_cc_cfg);
        uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, "mfb_cc_env", "m_config", mfb_cc_cfg);

        axi_cc_env    = uvm_pcie_axi::env_tx #(PCIE_ITEMS, uvm_pcie_axi::AXI_CC, DEVICE, STRADDLING)::type_id::create("axi_cc_env", this);
        mfb_cc_env    = uvm_logic_vector_array_mfb::env_rx #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, ITEM_WIDTH, 0)::type_id::create("mfb_cc_env", this);

        m_scoreboard = scoreboard::type_id::create("m_scoreboard", this);
        vscr         = uvm_pcie_cc_mfb2axi::virt_sequencer::type_id::create("vscr",this);
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);

        mfb_cc_env.analysis_port_data.connect(m_scoreboard.analysis_imp_mfb_cc);
        axi_cc_env.analysis_port.connect(m_scoreboard.cmp.analysis_imp_dut);

        m_reset.sync_connect(mfb_cc_env.reset_sync);
        m_reset.sync_connect(axi_cc_env.reset_sync);

        vscr.m_reset                  = m_reset.m_sequencer;
        vscr.m_logic_vector_array_scr = mfb_cc_env.m_sequencer.m_data;
    endfunction
endclass
