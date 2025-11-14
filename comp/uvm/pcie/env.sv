// env.sv: Verification environment
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class env_rx extends uvm_env;
    `uvm_component_param_utils(uvm_pcie::env_rx);

    uvm_analysis_port #(uvm_pcie::header) analysis_port;
    sequencer                             m_sequencer;
    uvm_reset::sync_cbs                   reset_sync;

    protected driver  m_driver;
    protected monitor m_monitor;

    protected stats m_stats;
    protected uvm_pcie::config_item m_config;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        reset_sync  = new();
    endfunction

    virtual function uvm_active_passive_enum get_is_active();
        return uvm_active_passive_enum'(m_config.active);
    endfunction

    function void build_phase(uvm_phase phase);
        // Get configurg file from
        if(!uvm_config_db #(config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(this.get_full_name(), "\n\tUnable to get configuration object")
        end

        super.build_phase(phase);

        if (get_is_active() == UVM_ACTIVE) begin
            m_sequencer = sequencer::type_id::create("m_sequencer" , this);
            m_driver    = driver::type_id::create("m_driver" , this);
        end else begin
            m_sequencer = null;
            m_driver    = null;
        end
        m_monitor   = monitor::type_id::create("m_monitor" , this);
        m_stats     = stats::type_id::create("m_stats", this);
    endfunction

    virtual function void bar_register(bar_config cfg);
        //if (get_is_active() == UVM_ACTIVE) begin
        //    //m_sequencer.bar_register(cfg);
        //end
        m_monitor.bar_register(cfg);
    endfunction

    function void connect_phase(uvm_phase phase);
        analysis_port = m_monitor.analysis_port;

        analysis_port.connect(m_stats.analysis_export);

        reset_sync.push_back(m_monitor.reset_sync);

        if (get_is_active() == UVM_ACTIVE) begin
            m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
        end
    endfunction
endclass


class env_tx extends uvm_env;
    `uvm_component_param_utils(uvm_pcie::env_tx);

    uvm_analysis_port #(uvm_pcie::header) analysis_port;
    uvm_reset::sync_cbs                   reset_sync;

    protected monitor m_monitor;

    protected stats m_stats;
    protected uvm_pcie::config_item m_config;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        reset_sync  = new();
    endfunction

    virtual function uvm_active_passive_enum get_is_active();
        return uvm_active_passive_enum'(m_config.active);
    endfunction

    function void build_phase(uvm_phase phase);
        // Get configurg file from
        if(!uvm_config_db #(config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(this.get_full_name(), "Unable to get configuration object")
        end

        super.build_phase(phase);

        m_monitor   = monitor::type_id::create("m_monitor" , this);
        m_stats     = stats::type_id::create("m_stats", this);
    endfunction

    virtual function void bar_register(bar_config cfg);
        m_monitor.bar_register(cfg);
    endfunction

    function void connect_phase(uvm_phase phase);
        analysis_port = m_monitor.analysis_port;

        analysis_port.connect(m_stats.analysis_export);

        reset_sync.push_back(m_monitor.reset_sync);
    endfunction
endclass


