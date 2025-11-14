// env.sv: Verification environment
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class root extends uvm_env;
    `uvm_component_param_utils(uvm_pcie::root);

    uvm_analysis_port #(uvm_pcie::header) analysis_port_cq;
    uvm_analysis_port #(uvm_pcie::header) analysis_port_cc;
    uvm_analysis_port #(uvm_pcie::header) analysis_port_rq;
    uvm_analysis_port #(uvm_pcie::header) analysis_port_rc;

    sequencer                             m_sequencer_cq;
    sequencer                             m_sequencer_rc;
    uvm_reset::sync_cbs                   reset_sync;

    protected uvm_pcie::config_item m_config;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        reset_sync  = new();
        m_sequencer_cq = null;
        m_sequencer_rc = null;
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

    endfunction

    virtual function void bar_register(bar_config cfg);
        //if (get_is_active() == UVM_ACTIVE) begin
        //    m_sequencer.bar_register(cfg);
        //end
        //m_monitor.bar_register(cfg);
    endfunction

endclass

