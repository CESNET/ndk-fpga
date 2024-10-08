/*
 * file       : agent.sv
 * Copyright (C) 2022 CESNET z. s. p. o.
 * description: General MII UVM Agent
 * date       : 2022
 * author     : Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef MII_AGENT_SV
`define MII_AGENT_SV

// This is MII agent, which declares basic components.
class agent_rx #(int unsigned CHANNELS, int unsigned WIDTH) extends uvm_agent;
    `uvm_component_param_utils(uvm_mii::agent_rx #(CHANNELS, WIDTH))

    // ------------------------------------------------------------------------
    // Variables
    uvm_analysis_port #(uvm_mii::sequence_item #(CHANNELS, WIDTH)) analysis_port;

    // ------------------------------------------------------------------------
    // Agent's base components
    uvm_mii::sequencer       #(CHANNELS, WIDTH) m_sequencer;
    uvm_mii::driver_rx          #(CHANNELS, WIDTH) m_driver;
    uvm_mii::monitor         #(CHANNELS, WIDTH) m_monitor;
    uvm_mii::config_item                        m_config;

    // ------------------------------------------------------------------------
    // Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);

        WHOLE_BYTES : assert((WIDTH & 7) == 0);
    endfunction

    // ------------------------------------------------------------------------
    // Functions
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        // Get configurg file from
        if(!uvm_config_db #(config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(this.get_full_name(), "Unable to get configuration object")
        end

        // Create sequencer and driver if the agent is active
        if(get_is_active() == UVM_ACTIVE) begin
            m_sequencer = sequencer #(CHANNELS, WIDTH)::type_id::create("m_sequencer", this);
            m_driver    = driver_rx #(CHANNELS, WIDTH)::type_id::create("m_driver", this);
        end

        // Create monitor
        m_monitor   = monitor #(CHANNELS, WIDTH)::type_id::create("m_monitor", this);
    endfunction

    virtual function uvm_active_passive_enum get_is_active();
        return uvm_active_passive_enum'(m_config.active);
    endfunction

    function void connect_phase(uvm_phase phase);

        // Interface to connect with
        virtual mii_if #(CHANNELS, WIDTH) vif;

        super.connect_phase(phase);

        // Get interface instance
        if(!uvm_config_db #(virtual mii_if #(CHANNELS, WIDTH))::get(null, "", m_config.interface_name, vif)) begin
            `uvm_fatal(this.get_full_name(), "Cannot find 'mii_if' inside uvm_config_db, probably not set!")
        end

        // Connect driver if the agent is active
        if(get_is_active() == UVM_ACTIVE) begin
            m_driver.vif = vif;
            m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
        end

        // Connect monitor
        m_monitor.vif = vif;
        analysis_port = m_monitor.analysis_port;
    endfunction

endclass

// This is MII agent, which declares basic components.
class agent_tx #(int unsigned CHANNELS, int unsigned WIDTH) extends uvm_agent;
    `uvm_component_param_utils(uvm_mii::agent_tx #(CHANNELS, WIDTH))

    // ------------------------------------------------------------------------
    // Variables
    uvm_analysis_port #(uvm_mii::sequence_item #(CHANNELS, WIDTH)) analysis_port;

    // ------------------------------------------------------------------------
    // Agent's base components
    uvm_mii::sequencer       #(CHANNELS, WIDTH) m_sequencer;
    uvm_mii::driver_tx          #(CHANNELS, WIDTH) m_driver;
    uvm_mii::monitor         #(CHANNELS, WIDTH) m_monitor;
    uvm_mii::config_item                        m_config;

    // ------------------------------------------------------------------------
    // Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);

        WHOLE_BYTES : assert((WIDTH & 7) == 0);
    endfunction

    // ------------------------------------------------------------------------
    // Functions
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        // Get configurg file from
        if(!uvm_config_db #(config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(this.get_full_name(), "Unable to get configuration object")
        end

        // Create sequencer and driver if the agent is active
        if(get_is_active() == UVM_ACTIVE) begin
            m_sequencer = sequencer #(CHANNELS, WIDTH)::type_id::create("m_sequencer", this);
            m_driver    = driver_tx #(CHANNELS, WIDTH)::type_id::create("m_driver", this);
        end

        // Create monitor
        m_monitor   = monitor #(CHANNELS, WIDTH)::type_id::create("m_monitor", this);
    endfunction

    virtual function uvm_active_passive_enum get_is_active();
        return uvm_active_passive_enum'(m_config.active);
    endfunction

    function void connect_phase(uvm_phase phase);

        // Interface to connect with
        virtual mii_if #(CHANNELS, WIDTH) vif;

        super.connect_phase(phase);

        // Get interface instance
        if(!uvm_config_db #(virtual mii_if #(CHANNELS, WIDTH))::get(null, "", m_config.interface_name, vif)) begin
            `uvm_fatal(this.get_full_name(), "Cannot find 'mii_if' inside uvm_config_db, probably not set!")
        end

        // Connect driver if the agent is active
        if(get_is_active() == UVM_ACTIVE) begin
            m_driver.vif = vif;
            m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
        end

        // Connect monitor
        m_monitor.vif = vif;
        analysis_port = m_monitor.analysis_port;
    endfunction

endclass


`endif
