/*
 * file       : env.sv
 * Copyright (C) 2022 CESNET z. s. p. o.
 * description: UVM Byte array to MII environment
 * date       : 2022
 * author     : Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class env_rx #(int unsigned CHANNELS, int unsigned CHANNEL_WIDTH) extends uvm_env;
    `uvm_component_param_utils(uvm_byte_array_mii::env_rx #(CHANNELS, CHANNEL_WIDTH))

    // High level agent
    uvm_byte_array::agent m_byte_array_agent;
    uvm_byte_array::config_item m_byte_array_agent_config;

    // Low level agent
    uvm_mii::agent_rx #(CHANNELS, CHANNEL_WIDTH) m_mii_agent;
    uvm_mii::config_item m_mii_agent_config;

    // Config for this environment
    uvm_byte_array_mii::config_item m_config;

    uvm_byte_array_mii::sequencer m_sequencer;
    uvm_byte_array_mii::monitor #(CHANNELS, CHANNEL_WIDTH)     m_monitor;

    function new(string name, uvm_component parent);
        super.new(name, parent);

        WHOLE_BYTES : assert((CHANNEL_WIDTH & 7) == 0);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        if(!uvm_config_db #(uvm_byte_array_mii::config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(this.get_full_name(), "[uvm_byte_array_mii::env] Unable to get configuration object")
        end

        m_byte_array_agent_config = new;
        m_mii_agent_config = new;

        m_byte_array_agent_config.active = m_config.active;

        m_mii_agent_config.active = m_config.active;
        m_mii_agent_config.interface_name = m_config.interface_name;

        uvm_config_db #(uvm_byte_array::config_item)::set(this, "m_byte_array_agent", "m_config", m_byte_array_agent_config);
        uvm_config_db #(uvm_mii::config_item)::set(this, "m_mii_agent", "m_config", m_mii_agent_config);

        uvm_byte_array::monitor::type_id::set_inst_override(monitor #(CHANNELS, CHANNEL_WIDTH)::get_type(), {this.get_full_name(), ".m_byte_array_agent.*"});

        m_byte_array_agent = uvm_byte_array::agent::type_id::create("m_byte_array_agent", this);
        m_mii_agent = uvm_mii::agent_rx #(CHANNELS, CHANNEL_WIDTH)::type_id::create("m_mii_agent", this);

        if (m_config.active == UVM_ACTIVE) begin
            m_sequencer  = uvm_byte_array_mii::sequencer::type_id::create("m_sequencer", this);
        end
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);

        uvm_config_db#(uvm_byte_array_mii::sequencer)::set(this, "m_mii_agent.m_sequencer" , "hi_sqr", m_sequencer);

        $cast(this.m_monitor, m_byte_array_agent.m_monitor);
        m_mii_agent.analysis_port.connect(m_monitor.analysis_export);

        if (m_config.active == UVM_ACTIVE) begin
            m_sequencer.byte_array_sequencer = m_byte_array_agent.m_sequencer;
        end
    endfunction

    virtual task run_phase(uvm_phase phase);
        if (m_config.active == UVM_ACTIVE) begin
            uvm_byte_array_mii::sequence_lib_rx #(CHANNELS, CHANNEL_WIDTH) seq_lib = uvm_byte_array_mii::sequence_lib_rx #(CHANNELS, CHANNEL_WIDTH)::type_id::create("sequence_library");
            seq_lib.min_random_count = 1;
            seq_lib.max_random_count = 50;
            seq_lib.load_sequences();

            forever begin
                if(!seq_lib.randomize()) `uvm_fatal(this.get_full_name(), "\n\tCannot randomize byte_array_lii rx_seq");
                seq_lib.start(m_mii_agent.m_sequencer);
            end
        end
    endtask
endclass

class env_tx #(int unsigned CHANNELS, int unsigned CHANNEL_WIDTH) extends uvm_env;
    `uvm_component_param_utils(uvm_byte_array_mii::env_tx #(CHANNELS, CHANNEL_WIDTH))

    // High level agent
    uvm_byte_array::agent m_byte_array_agent;
    uvm_byte_array::config_item m_byte_array_agent_config;

    // Low level agent
    uvm_mii::agent_tx #(CHANNELS, CHANNEL_WIDTH) m_mii_agent;
    uvm_mii::config_item m_mii_agent_config;

    // Config for this environment
    uvm_byte_array_mii::config_item m_config;

    uvm_byte_array_mii::monitor #(CHANNELS, CHANNEL_WIDTH)     m_monitor;

    function new(string name, uvm_component parent);
        super.new(name, parent);

        WHOLE_BYTES : assert((CHANNEL_WIDTH & 7) == 0);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        if(!uvm_config_db #(uvm_byte_array_mii::config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(this.get_full_name(), "[uvm_byte_array_mii::env] Unable to get configuration object")
        end

        m_byte_array_agent_config = new;
        m_mii_agent_config = new;

        m_byte_array_agent_config.active = UVM_PASSIVE;

        m_mii_agent_config.active = m_config.active;
        m_mii_agent_config.interface_name = m_config.interface_name;

        uvm_config_db #(uvm_byte_array::config_item)::set(this, "m_byte_array_agent", "m_config", m_byte_array_agent_config);
        uvm_config_db #(uvm_mii::config_item)::set(this, "m_mii_agent", "m_config", m_mii_agent_config);

        uvm_byte_array::monitor::type_id::set_inst_override(monitor #(CHANNELS, CHANNEL_WIDTH)::get_type(), {this.get_full_name(), ".m_byte_array_agent.*"});

        m_byte_array_agent = uvm_byte_array::agent::type_id::create("m_byte_array_agent", this);
        m_mii_agent = uvm_mii::agent_tx #(CHANNELS, CHANNEL_WIDTH)::type_id::create("m_mii_agent", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);

        $cast(this.m_monitor, m_byte_array_agent.m_monitor);
        m_mii_agent.analysis_port.connect(m_monitor.analysis_export);
    endfunction

    virtual task run_phase(uvm_phase phase);
        if (m_config.active == UVM_ACTIVE) begin
            uvm_byte_array_mii::sequence_lib_tx #(CHANNELS, CHANNEL_WIDTH) seq_lib = uvm_byte_array_mii::sequence_lib_tx #(CHANNELS, CHANNEL_WIDTH)::type_id::create("sequence_library_tx");
            seq_lib.min_random_count = 1;
            seq_lib.max_random_count = 50;
            seq_lib.load_sequences();

            forever begin
                if(!seq_lib.randomize()) `uvm_fatal(this.get_full_name(), "\n\tCannot randomize byte_array_lii rx_seq");
                seq_lib.start(m_mii_agent.m_sequencer);
            end
        end
    endtask
endclass
