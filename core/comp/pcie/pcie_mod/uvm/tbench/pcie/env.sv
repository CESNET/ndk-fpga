// env.sv: Verification environment
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class env extends uvm_env;
    `uvm_component_param_utils(uvm_pcie::env);

    uvm_analysis_port #(uvm_pcie::request_header)   cq_analysis_port;
    uvm_analysis_port #(uvm_pcie::completer_header) cc_analysis_port;
    uvm_analysis_port #(uvm_pcie::request_header)   rq_analysis_port;
    uvm_analysis_port #(uvm_pcie::completer_header) rc_analysis_port;

    sequencer                             m_sequencer;
    uvm_reset::sync_cbs                   reset_sync;

    protected driver  m_driver;
    protected monitor m_monitor;

    protected stats m_stats;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction


    function void build_phase(uvm_phase phase);
        m_sequencer = sequencer::type_id::create("m_sequencer" , this);
        m_driver    = driver::type_id::create("m_driver" , this);
        m_monitor   = monitor::type_id::create("m_monitor" , this);
        m_stats     = stats::type_id::create("m_stats", this);
        reset_sync  = new();
    endfunction

    function void connect_phase(uvm_phase phase);
        cq_analysis_port = m_monitor.cq_analysis_port;
        cc_analysis_port = m_monitor.cc_analysis_port;
        rq_analysis_port = m_monitor.rq_analysis_port;
        rc_analysis_port = m_monitor.rc_analysis_port;

        cq_analysis_port.connect(m_stats.cq_analysis_export);
        cc_analysis_port.connect(m_stats.cc_analysis_export);
        rq_analysis_port.connect(m_stats.rq_analysis_export);
        rc_analysis_port.connect(m_stats.rc_analysis_export);

        m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
        cc_analysis_port.connect(m_sequencer.fifo_cc.analysis_export);
        rq_analysis_port.connect(m_sequencer.fifo_rq.analysis_export);
    endfunction


endclass


