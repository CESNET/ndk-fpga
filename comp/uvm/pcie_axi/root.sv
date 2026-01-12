// env.sv: Verification environment
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class root#(
    int unsigned AXI_ITEMS,
    string DEVICE,
    logic STRADDLING
) extends uvm_pcie::root;
    `uvm_component_param_utils(uvm_pcie_axi::root#(AXI_ITEMS, DEVICE, STRADDLING));

    localparam CQ_STRADDLING = 0;
    localparam CC_STRADDLING = 0;
    localparam RQ_STRADDLING = 1; //RQ have allways enabled straddling
    localparam RC_STRADDLING = 1;

    protected uvm_pcie_axi::env_rx#(AXI_ITEMS, uvm_pcie_axi::AXI_CQ, DEVICE, CQ_STRADDLING) m_cq;
    protected uvm_pcie_axi::env_tx#(AXI_ITEMS, uvm_pcie_axi::AXI_CC, DEVICE, CC_STRADDLING) m_cc;
    protected uvm_pcie_axi::env_tx#(AXI_ITEMS, uvm_pcie_axi::AXI_RQ, DEVICE, RQ_STRADDLING) m_rq;
    protected uvm_pcie_axi::env_rx#(AXI_ITEMS, uvm_pcie_axi::AXI_RC, DEVICE, RC_STRADDLING) m_rc;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        reset_sync  = new();
    endfunction

    virtual function uvm_active_passive_enum get_is_active();
        return uvm_active_passive_enum'(m_config.active);
    endfunction

    function void build_phase(uvm_phase phase);
        uvm_pcie::config_item  m_cq_cfg;
        uvm_pcie::config_item  m_cc_cfg;
        uvm_pcie::config_item  m_rq_cfg;
        uvm_pcie::config_item  m_rc_cfg;

        super.build_phase(phase);

        m_cq_cfg    = new();
        m_cq_cfg.interface_name    = {m_config.interface_name, "_cq"};
        m_cq_cfg.active    = UVM_ACTIVE;
        uvm_config_db #(uvm_pcie::config_item)::set(this, "m_cq", "m_config", m_cq_cfg);
        m_cq = uvm_pcie_axi::env_rx#(AXI_ITEMS, uvm_pcie_axi::AXI_CQ, DEVICE, CQ_STRADDLING)::type_id::create("m_cq", this);

        m_cc_cfg    = new();
        m_cc_cfg.interface_name    = {m_config.interface_name, "_cc"};
        m_cc_cfg.active    = UVM_ACTIVE;
        uvm_config_db #(uvm_pcie::config_item)::set(this, "m_cc", "m_config", m_cc_cfg);
        m_cc = uvm_pcie_axi::env_tx#(AXI_ITEMS, uvm_pcie_axi::AXI_CC, DEVICE, CC_STRADDLING)::type_id::create("m_cc", this);

        m_rq_cfg    = new();
        m_rq_cfg.interface_name    = {m_config.interface_name, "_rq"};
        m_rq_cfg.active    = UVM_ACTIVE;
        uvm_config_db #(uvm_pcie::config_item)::set(this, "m_rq", "m_config", m_rq_cfg);
        m_rq = uvm_pcie_axi::env_tx#(AXI_ITEMS, uvm_pcie_axi::AXI_RQ, DEVICE, RQ_STRADDLING)::type_id::create("m_rq", this);

        m_rc_cfg    = new();
        m_rc_cfg.interface_name    = {m_config.interface_name, "_rc"};
        m_rc_cfg.active    = UVM_ACTIVE;
        uvm_config_db #(uvm_pcie::config_item)::set(this, "m_rc", "m_config", m_rc_cfg);
        m_rc = uvm_pcie_axi::env_rx#(AXI_ITEMS, uvm_pcie_axi::AXI_RC, DEVICE, RC_STRADDLING)::type_id::create("m_rc", this);
    endfunction

    virtual function void bar_register(uvm_pcie::bar_config cfg);
        m_cq.bar_register(cfg);
        m_cc.bar_register(cfg);
        m_rq.bar_register(cfg);
        m_rc.bar_register(cfg);
    endfunction

    function void connect_phase(uvm_phase phase);
        analysis_port_cq = m_cq.analysis_port;
        analysis_port_cc = m_cc.analysis_port;
        analysis_port_rq = m_rq.analysis_port;
        analysis_port_rc = m_rc.analysis_port;

        m_sequencer_cq = m_cq.m_sequencer;
        m_sequencer_rc = m_rc.m_sequencer;

        reset_sync.push_back(m_cq.reset_sync);
        reset_sync.push_back(m_cc.reset_sync);
        reset_sync.push_back(m_rq.reset_sync);
        reset_sync.push_back(m_rc.reset_sync);
    endfunction
endclass

