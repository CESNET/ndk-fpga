// agent.sv
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): David Beneš <xbenes52@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class agent #(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH) extends uvm_agent;
    `uvm_component_param_utils(uvm_meta::agent #(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH))

    // -----------------------
    // Variables.
    // -----------------------
    uvm_analysis_port #(sequence_item #(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH)) analysis_port;
    monitor #(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH)     m_monitor;
    sequencer #(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH)   m_sequencer;
    config_item m_config;

    // Contructor, where analysis port is created.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction: new

    // -----------------------
    // Functions.
    // -----------------------
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        if (!uvm_config_db #(config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(this.get_full_name(), "Cannot get configuration object")
        end

        m_monitor = monitor#(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH)::type_id::create("m_monitor", this);
        if(get_is_active() == UVM_ACTIVE) begin
            m_sequencer = sequencer#(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH)::type_id::create("m_sequencer", this);
        end
    endfunction

    virtual function uvm_active_passive_enum get_is_active();
        return uvm_active_passive_enum'(m_config.active);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        analysis_port = m_monitor.analysis_port;
    endfunction

endclass
