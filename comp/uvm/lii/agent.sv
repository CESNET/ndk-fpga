/*
 * file       : agent.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: LII agent
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef LII_AGENT_SV
`define LII_AGENT_SV

// This is LII agent, which declares basic components.
class agent_rx #(int unsigned DATA_WIDTH, logic FAST_SOF, int unsigned META_WIDTH, int unsigned SOF_WIDTH) extends uvm_agent;

    // Registration of agent to databaze.
    `uvm_component_param_utils(uvm_lii::agent_rx #(DATA_WIDTH, FAST_SOF, META_WIDTH, SOF_WIDTH))

    // -----------------------
    // Variables.
    // -----------------------

    uvm_analysis_port #(sequence_item #(DATA_WIDTH, META_WIDTH, SOF_WIDTH)) analysis_port;

    // Agent base components sequencer, driver, monitor.
    sequencer #(DATA_WIDTH, META_WIDTH, SOF_WIDTH) m_sequencer;
    driver_rx #(DATA_WIDTH, FAST_SOF, META_WIDTH, SOF_WIDTH) m_driver;
    monitor #(DATA_WIDTH, FAST_SOF, META_WIDTH, SOF_WIDTH) m_monitor;
    config_item m_config;

    // Constructor.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction: new

    // -----------------------
    // Functions.
    // -----------------------

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        if(!uvm_config_db #(config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(get_type_name(), "Unable to get configuration object")
        end

        if(get_is_active() == UVM_ACTIVE) begin
            m_sequencer = sequencer #(DATA_WIDTH, META_WIDTH, SOF_WIDTH)::type_id::create("m_sequencer", this);
            m_driver    = driver_rx #(DATA_WIDTH, FAST_SOF, META_WIDTH, SOF_WIDTH)::type_id::create("m_driver", this);
        end
        m_monitor   = monitor #(DATA_WIDTH, FAST_SOF, META_WIDTH, SOF_WIDTH)::type_id::create("m_monitor", this);
    endfunction

    virtual function uvm_active_passive_enum get_is_active();
        return uvm_active_passive_enum'(m_config.active);
    endfunction

    function void connect_phase(uvm_phase phase);

        virtual lii_if #(DATA_WIDTH, FAST_SOF, META_WIDTH, SOF_WIDTH) vif;
        super.connect_phase(phase);

        if(!uvm_config_db #(virtual lii_if #(DATA_WIDTH, FAST_SOF, META_WIDTH, SOF_WIDTH))::get(null, "", m_config.interface_name, vif)) begin
            `uvm_fatal(this.get_full_name(), "Cannot find 'lii_interface' inside uvm_config_db, probably not set!")
        end

        // Connect.
        m_monitor.vif = vif;
        analysis_port = m_monitor.analysis_port;
        // Driver.
        if(get_is_active() == UVM_ACTIVE) begin
            m_driver.vif = vif;
            m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
        end
    endfunction

endclass


// This is LII agent, which declares basic components.
class agent_tx #(int unsigned DATA_WIDTH, logic FAST_SOF, int unsigned META_WIDTH, int unsigned SOF_WIDTH) extends uvm_agent;

    // Registration of agent to databaze.
    `uvm_component_param_utils(uvm_lii::agent_tx #(DATA_WIDTH, FAST_SOF, META_WIDTH, SOF_WIDTH))

    // -----------------------
    // Variables.
    // -----------------------

    uvm_analysis_port #(sequence_item #(DATA_WIDTH, META_WIDTH, SOF_WIDTH)) analysis_port;

    // Agent base components sequencer, driver, monitor.
    sequencer #(DATA_WIDTH, META_WIDTH, SOF_WIDTH) m_sequencer;
    driver_tx #(DATA_WIDTH, FAST_SOF, META_WIDTH, SOF_WIDTH) m_driver;
    monitor #(DATA_WIDTH, FAST_SOF, META_WIDTH, SOF_WIDTH) m_monitor;
    config_item m_config;

    // Constructor.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction: new

    // -----------------------
    // Functions.
    // -----------------------

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        if(!uvm_config_db #(config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(get_type_name(), "Unable to get configuration object")
        end

        if(get_is_active() == UVM_ACTIVE) begin
            m_sequencer = sequencer #(DATA_WIDTH, META_WIDTH, SOF_WIDTH)::type_id::create("m_sequencer", this);
            m_driver    = driver_tx #(DATA_WIDTH, FAST_SOF, META_WIDTH, SOF_WIDTH)::type_id::create("m_driver", this);
        end
        m_monitor   = monitor #(DATA_WIDTH, FAST_SOF, META_WIDTH, SOF_WIDTH)::type_id::create("m_monitor", this);
    endfunction

    virtual function uvm_active_passive_enum get_is_active();
        return uvm_active_passive_enum'(m_config.active);
    endfunction

    function void connect_phase(uvm_phase phase);

        virtual lii_if #(DATA_WIDTH, FAST_SOF, META_WIDTH, SOF_WIDTH) vif;
        super.connect_phase(phase);

        if(!uvm_config_db #(virtual lii_if #(DATA_WIDTH, FAST_SOF, META_WIDTH, SOF_WIDTH))::get(null, "", m_config.interface_name, vif)) begin
            $write("Interface name %s interface %p\n", m_config.interface_name, vif);
            `uvm_fatal("configuration", "Cannot find 'lii_interface' inside uvm_config_db, probably not set!")
        end

        // Connect.
        m_monitor.vif = vif;
        analysis_port = m_monitor.analysis_port;
        // Driver.
        if(get_is_active() == UVM_ACTIVE) begin
            m_driver.vif = vif;
            m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
        end
    endfunction

endclass

// This is ETH PHY agent, which declares basic components.
class agent_rx_eth_phy #(int unsigned DATA_WIDTH, logic FAST_SOF, int unsigned META_WIDTH, logic MEAS, int unsigned SOF_WIDTH) extends uvm_agent;

    // Registration of agent to databaze.
    `uvm_component_param_utils(uvm_lii::agent_rx_eth_phy #(DATA_WIDTH, FAST_SOF, META_WIDTH, MEAS, SOF_WIDTH))
    // Variables.

    uvm_analysis_port #(sequence_item #(DATA_WIDTH, META_WIDTH, SOF_WIDTH)) analysis_port;

    // Agent base components sequencer, driver, monitor.
    sequencer #(DATA_WIDTH, META_WIDTH, SOF_WIDTH) m_sequencer;
    driver_rx_eth_phy #(DATA_WIDTH, FAST_SOF, META_WIDTH, MEAS, SOF_WIDTH) m_driver;
    monitor #(DATA_WIDTH, FAST_SOF, META_WIDTH, SOF_WIDTH) m_monitor;
    config_item m_config;

    // Constructor.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction: new

    // -----------------------
    // Functions.
    // -----------------------

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        if(!uvm_config_db #(config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(get_type_name(), "Unable to get configuration object")
        end

        if(get_is_active() == UVM_ACTIVE) begin
            m_sequencer = sequencer #(DATA_WIDTH, META_WIDTH, SOF_WIDTH)::type_id::create("m_sequencer", this);
            m_driver    = driver_rx_eth_phy #(DATA_WIDTH, FAST_SOF, META_WIDTH, MEAS, SOF_WIDTH)::type_id::create("m_driver", this);
        end
        m_monitor   = monitor #(DATA_WIDTH, FAST_SOF, META_WIDTH, SOF_WIDTH)::type_id::create("m_monitor", this);
    endfunction

    virtual function uvm_active_passive_enum get_is_active();
        return uvm_active_passive_enum'(m_config.active);
    endfunction

    function void connect_phase(uvm_phase phase);

        virtual lii_if #(DATA_WIDTH, FAST_SOF, META_WIDTH, SOF_WIDTH) vif;
        super.connect_phase(phase);

        if(!uvm_config_db #(virtual lii_if #(DATA_WIDTH, FAST_SOF, META_WIDTH, SOF_WIDTH))::get(null, "", m_config.interface_name, vif)) begin
            $write("Interface name %s interface %p\n", m_config.interface_name, vif);
            `uvm_fatal("configuration", "Cannot find 'lii_interface' inside uvm_config_db, probably not set!")
        end

        // Connect.
        m_monitor.vif = vif;
        analysis_port = m_monitor.analysis_port;
        // Driver.
        if(get_is_active() == UVM_ACTIVE) begin
            m_driver.vif = vif;
            m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
        end
    endfunction

endclass

`endif
