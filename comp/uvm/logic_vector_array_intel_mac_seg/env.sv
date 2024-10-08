/*
 * file       : monitor.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: convert byte array to intel mac seq
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


class env_rx #(int unsigned SEGMENTS) extends uvm_env;
    `uvm_component_param_utils(uvm_logic_vector_array_intel_mac_seg::env_rx#(SEGMENTS))

    // fcs_error, tr.error, tr.status_data
    localparam LOGIC_WIDTH = 6;
    localparam ITEM_WIDTH = 8;

    //exporting
    uvm_analysis_port #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)) analysis_port_packet;
    uvm_analysis_port #(uvm_logic_vector::sequence_item#(LOGIC_WIDTH)) analysis_port_error;
    sequencer                                      m_sequencer;
    uvm_reset::sync_cbs                                reset_sync;

    // high level agent
    uvm_logic_vector_array::agent#(ITEM_WIDTH)       m_byte_array_agent;
    uvm_logic_vector_array::config_item m_byte_array_cfg;

    uvm_logic_vector::agent #(LOGIC_WIDTH) m_logic_vector_agent;
    uvm_logic_vector::config_item         m_logic_vector_cfg;

    // low level aget
    uvm_intel_mac_seg::agent_rx #(SEGMENTS) m_intel_mac_seg_agent;
    uvm_intel_mac_seg::config_item          m_intel_mac_seg_cfg;

    config_item m_config;

    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        if(!uvm_config_db #(config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(this.get_full_name(), "Unable to get configuration object")
        end

        //create byte array agent
        m_byte_array_cfg = new;
        m_byte_array_cfg.active = m_config.active;
        uvm_config_db #(uvm_logic_vector_array::config_item)::set(this, "m_byte_array_agent", "m_config", m_byte_array_cfg);
        uvm_logic_vector_array::monitor#(ITEM_WIDTH)::type_id::set_inst_override(monitor_byte_array#(SEGMENTS)::get_type(), {this.get_full_name(), ".m_byte_array_agent.*"});
        m_byte_array_agent    = uvm_logic_vector_array::agent#(ITEM_WIDTH)::type_id::create("m_byte_array_agent", this);

        //create logic vector
        m_logic_vector_cfg = new;
        m_logic_vector_cfg.active = m_config.active;
        uvm_config_db #(uvm_logic_vector::config_item)::set(this, "m_logic_vector_agent", "m_config", m_logic_vector_cfg);
        uvm_logic_vector::monitor#(LOGIC_WIDTH)::type_id::set_inst_override(monitor_logic_vector#(LOGIC_WIDTH, SEGMENTS)::get_type(), {this.get_full_name(), ".m_logic_vector_agent.*"});
        m_logic_vector_agent = uvm_logic_vector::agent #(LOGIC_WIDTH)::type_id::create("m_logic_vector_agent", this);

        //create intel seq mac agent
        m_intel_mac_seg_cfg = new;
        m_intel_mac_seg_cfg.active         = m_config.active;
        m_intel_mac_seg_cfg.interface_name = m_config.interface_name;
        uvm_config_db #(uvm_intel_mac_seg::config_item)::set(this, "m_intel_mac_seg_agent", "m_config", m_intel_mac_seg_cfg);
        m_intel_mac_seg_agent = uvm_intel_mac_seg::agent_rx #(SEGMENTS)::type_id::create("m_intel_mac_seg_agent", this);

        if (m_config.active == UVM_ACTIVE) begin
            m_sequencer = sequencer::type_id::create("m_sequencer", this);
        end

        reset_sync = new();
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);
        monitor_byte_array   #(SEGMENTS) env_monitor_byte_array;
        monitor_logic_vector #(LOGIC_WIDTH, SEGMENTS) env_monitor_logic_vector;

        $cast(env_monitor_byte_array, m_byte_array_agent.m_monitor);
        m_intel_mac_seg_agent.analysis_port.connect(env_monitor_byte_array.analysis_export);
        reset_sync.push_back(env_monitor_byte_array.reset_sync);

        $cast(env_monitor_logic_vector, m_logic_vector_agent.m_monitor);
        m_intel_mac_seg_agent.analysis_port.connect(env_monitor_logic_vector.analysis_export);
        reset_sync.push_back(env_monitor_logic_vector.reset_sync);

        analysis_port_packet   = m_byte_array_agent.analysis_port;
        analysis_port_error = m_logic_vector_agent.analysis_port;
        if (m_config.active == UVM_ACTIVE) begin
            reset_sync.push_back(m_intel_mac_seg_agent.m_sequencer.reset_sync);
            m_sequencer.m_packet = m_byte_array_agent.m_sequencer;
            m_sequencer.m_error  = m_logic_vector_agent.m_sequencer;
            //add high level sequencer to configuration database
            uvm_config_db#(sequencer)::set(this, "m_intel_mac_seg_agent.m_sequencer" , "hl_sqr", m_sequencer);
        end

    endfunction

    virtual task run_phase(uvm_phase phase);
        if (m_config.active == UVM_ACTIVE) begin
            sequence_lib_rx#(SEGMENTS) intel_mac_seg;
            intel_mac_seg = sequence_lib_rx#(SEGMENTS)::type_id::create("avalon_rx_seq_base", this);
            intel_mac_seg.init_sequence();
            intel_mac_seg.min_random_count = 20;
            intel_mac_seg.max_random_count = 100;

            forever begin
                if(!intel_mac_seg.randomize()) `uvm_fatal(this.get_full_name(), "\n\tCannot randomize byte_array_intel_mac_seg rx_seq");
                intel_mac_seg.start(m_intel_mac_seg_agent.m_sequencer);
            end
        end
    endtask
endclass


class env_tx #(int unsigned SEGMENTS) extends uvm_env;
    `uvm_component_param_utils(uvm_logic_vector_array_intel_mac_seg::env_tx#(SEGMENTS))

    // fcs_error, tr.error, tr.status_data
    localparam LOGIC_WIDTH = 6;
    localparam ITEM_WIDTH = 8;

    uvm_analysis_port #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH))                 analysis_port_packet;
    uvm_analysis_port #(uvm_logic_vector::sequence_item#(LOGIC_WIDTH)) analysis_port_error;

    uvm_intel_mac_seg::sequencer#(SEGMENTS)            m_sequencer;

    //high level agents
    uvm_logic_vector_array::agent#(ITEM_WIDTH)       m_byte_array_agent;
    uvm_logic_vector_array::config_item              m_byte_array_cfg;

    uvm_logic_vector::agent#(LOGIC_WIDTH) m_logic_vector_agent;
    uvm_logic_vector::config_item         m_logic_vector_cfg;
    //RESET
    uvm_reset::sync_cbs                                reset_sync;

    // Definition of agents, LII agents are used on both sides.
    uvm_intel_mac_seg::agent_tx #(SEGMENTS) m_intel_mac_seg_agent;
    uvm_intel_mac_seg::config_item          m_intel_mac_seg_cfg;

    config_item m_config;

    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        if(!uvm_config_db #(config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(this.get_full_name(), "Unable to get configuration object")
        end

        //create byte array agent
        m_byte_array_cfg = new;
        m_byte_array_cfg.active = UVM_PASSIVE;
        uvm_config_db #(uvm_logic_vector_array::config_item)::set(this, "m_byte_array_agent", "m_config", m_byte_array_cfg);
        uvm_logic_vector_array::monitor#(ITEM_WIDTH)::type_id::set_inst_override(monitor_byte_array#(SEGMENTS)::get_type(), {this.get_full_name(), ".m_byte_array_agent.*"});
        m_byte_array_agent    = uvm_logic_vector_array::agent#(ITEM_WIDTH)::type_id::create("m_byte_array_agent", this);

        //create logic vector
        m_logic_vector_cfg = new;
        m_logic_vector_cfg.active = UVM_PASSIVE;
        uvm_config_db #(uvm_logic_vector::config_item)::set(this, "m_logic_vector_agent", "m_config", m_logic_vector_cfg);
        uvm_logic_vector::monitor#(LOGIC_WIDTH)::type_id::set_inst_override(monitor_logic_vector#(LOGIC_WIDTH, SEGMENTS)::get_type(), {this.get_full_name(), ".m_logic_vector_agent.*"});
        m_logic_vector_agent = uvm_logic_vector::agent #(LOGIC_WIDTH)::type_id::create("m_logic_vector_agent", this);

        //create intel seq mac agent
        m_intel_mac_seg_cfg = new;
        m_intel_mac_seg_cfg.active         = m_config.active;
        m_intel_mac_seg_cfg.interface_name = m_config.interface_name;
        uvm_config_db #(uvm_intel_mac_seg::config_item)::set(this, "m_intel_mac_seg_agent", "m_config", m_intel_mac_seg_cfg);
        m_intel_mac_seg_agent = uvm_intel_mac_seg::agent_tx #(SEGMENTS)::type_id::create("m_intel_mac_seg_agent", this);

        reset_sync = new();
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);
        monitor_byte_array #(SEGMENTS) env_monitor_packet;
        monitor_logic_vector #(LOGIC_WIDTH, SEGMENTS) env_monitor_error;

        $cast(env_monitor_packet, m_byte_array_agent.m_monitor);
        m_intel_mac_seg_agent.analysis_port.connect(env_monitor_packet.analysis_export);
        reset_sync.push_back(env_monitor_packet.reset_sync);

        $cast(env_monitor_error, m_logic_vector_agent.m_monitor);
        m_intel_mac_seg_agent.analysis_port.connect(env_monitor_error.analysis_export);
        reset_sync.push_back(env_monitor_error.reset_sync);


        analysis_port_packet = m_byte_array_agent.analysis_port;
        analysis_port_error  = m_logic_vector_agent.analysis_port;
        if (m_config.active == UVM_ACTIVE) begin
            reset_sync.push_back(m_intel_mac_seg_agent.m_sequencer.reset_sync);
            m_sequencer = m_intel_mac_seg_agent.m_sequencer;
        end
    endfunction
endclass
