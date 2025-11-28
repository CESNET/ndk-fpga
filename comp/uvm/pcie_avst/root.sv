// env.sv: Verification environment
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class monitor_root extends uvm_monitor;
    `uvm_component_param_utils(uvm_pcie_avst::monitor_root);

    uvm_analysis_port #(uvm_pcie::header) analysis_port_req;
    uvm_analysis_port #(uvm_pcie::header) analysis_port_res;

    uvm_analysis_imp#(uvm_pcie::header, monitor_root) pcie_export;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        analysis_port_req = new("analysis_port_req", this);
        analysis_port_res = new("analysis_port_res", this);

        pcie_export = new("pcie_export", this);
    endfunction

    function void write(uvm_pcie::header t);

        unique case (t.hdr_type)
            uvm_pcie::header::RQ_HDR        : analysis_port_req.write(t);
            uvm_pcie::header::COMPLETER_HDR : analysis_port_res.write(t);
            default                         : `uvm_fatal(this.get_full_name(), "\n\tUnsupported HEADER")
        endcase
    endfunction

endclass

class sequence_root extends uvm_sequence#(uvm_pcie::header);
    `uvm_object_param_utils(uvm_pcie_avst::sequence_root);

    uvm_sequencer#(uvm_pcie::header) hl_sqr;

    function new(string name = "uvm_pcie_avst::sequence_root");
        super.new(name);
        hl_sqr = null;
    endfunction

    task body();
        forever begin
            uvm_pcie::header orig;
            hl_sqr.get_next_item(orig);
            $cast(req, orig.clone());

            start_item(req);
            finish_item(req);
            hl_sqr.item_done();
        end
    endtask
endclass


class root#(
    int unsigned REGIONS,
    int unsigned REGIONS_SIZE,
    int unsigned RDY_LATENCY,
    logic STRADDLING
) extends uvm_pcie::root;
    `uvm_component_param_utils(uvm_pcie_avst::root#(REGIONS, REGIONS_SIZE, RDY_LATENCY, STRADDLING));

    parameter AVST_META_UP   = 128 + 32 + 1; //HDR + PREFIX + ERROR
    parameter AVST_META_DOWN = 128 + 32 + 3; //HDR + PREFIX + BAR

    // MONITOR SPLITTER
    protected monitor_root m_monitor_down;
    protected monitor_root m_monitor_up;

    protected uvm_pcie_avst::env_rx #(REGIONS, REGIONS_SIZE, AVST_META_DOWN, RDY_LATENCY, STRADDLING) m_avst_down;
    protected uvm_pcie_avst::env_tx #(REGIONS, REGIONS_SIZE, AVST_META_UP, STRADDLING)                m_avst_up;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        reset_sync  = new();
    endfunction

    virtual function uvm_active_passive_enum get_is_active();
        return uvm_active_passive_enum'(m_config.active);
    endfunction

    function void build_phase(uvm_phase phase);
        uvm_pcie::config_item  m_avst_up_cfg;
        uvm_pcie::config_item  m_avst_down_cfg;

        super.build_phase(phase);

        m_sequencer_cq = uvm_pcie::sequencer::type_id::create("m_sequencer_cq", this);
        m_sequencer_rc = uvm_pcie::sequencer::type_id::create("m_sequencer_rc", this);

        m_monitor_down = monitor_root::type_id::create("m_monitor_down", this);
        m_monitor_up   = monitor_root::type_id::create("m_monitor_up", this);

        m_avst_down_cfg    = new();
        m_avst_down_cfg.interface_name    = {m_config.interface_name, "_down"};
        m_avst_down_cfg.active    = UVM_ACTIVE;
        uvm_config_db #(uvm_pcie::config_item)::set(this, "m_avst_down", "m_config", m_avst_down_cfg);
        m_avst_down = uvm_pcie_avst::env_rx #(REGIONS, REGIONS_SIZE, AVST_META_DOWN, RDY_LATENCY, STRADDLING)::type_id::create("m_avst_down", this);

        m_avst_up_cfg    = new();
        m_avst_up_cfg.interface_name    = {m_config.interface_name, "_up"};
        m_avst_up_cfg.active    = UVM_ACTIVE;
        uvm_config_db #(uvm_pcie::config_item)::set(this, "m_avst_up", "m_config", m_avst_up_cfg);
        m_avst_up = uvm_pcie_avst::env_tx #(REGIONS, REGIONS_SIZE, AVST_META_UP, STRADDLING)::type_id::create("m_avst_up", this);
    endfunction

    virtual function void bar_register(uvm_pcie::bar_config cfg);
        m_avst_down.bar_register(cfg);
        m_avst_up  .bar_register(cfg);
    endfunction

    function void connect_phase(uvm_phase phase);
        analysis_port_cq = m_monitor_down.analysis_port_req;
        analysis_port_cc = m_monitor_up.analysis_port_res;
        analysis_port_rq = m_monitor_up.analysis_port_req;
        analysis_port_rc = m_monitor_down.analysis_port_res;

        m_avst_down.analysis_port.connect(m_monitor_down.pcie_export);
        m_avst_up.analysis_port.connect(m_monitor_up.pcie_export);

        reset_sync.push_back(m_avst_up.reset_sync);
        reset_sync.push_back(m_avst_down.reset_sync);
    endfunction

    task run_phase(uvm_phase phase);
        sequence_root req;
        sequence_root res;

        req = sequence_root::type_id::create("req", this);
        req.hl_sqr = m_sequencer_cq;
        res = sequence_root::type_id::create("res", this);
        res.hl_sqr = m_sequencer_rc;

        fork
            forever begin
                assert(req.randomize()) else `uvm_fatal(this.get_full_name(), "\n\tCannot randomize seqeunce");
                req.start(m_avst_down.m_sequencer);
            end

            forever begin
                assert(res.randomize()) else `uvm_fatal(this.get_full_name(), "\n\tCannot randomize seqeunce");
                res.start(m_avst_down.m_sequencer);
            end
        join
    endtask
endclass

