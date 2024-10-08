/*
 * file       : env.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: uvm_byte_array to uvm_lii enviroment
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef RX_ENV_SV
`define RX_ENV_SV

class env_rx #(int unsigned DATA_WIDTH, logic FAST_SOF, logic DIC_EN, int unsigned VERBOSITY, int unsigned META_WIDTH, int unsigned LOGIC_WIDTH, int unsigned SOF_WIDTH) extends uvm_env;

    `uvm_component_param_utils(uvm_byte_array_lii::env_rx #(DATA_WIDTH, FAST_SOF, DIC_EN, VERBOSITY, META_WIDTH, LOGIC_WIDTH, SOF_WIDTH));

    uvm_analysis_port #(uvm_byte_array::sequence_item) analysis_port_packet;
    uvm_analysis_port #(uvm_logic_vector::sequence_item#(LOGIC_WIDTH)) analysis_port_meta;
    uvm_byte_array_lii::sequencer #(LOGIC_WIDTH) m_sequencer;

    // Definition of agents, high level agents are used on both sides.
    uvm_byte_array::agent m_byte_array_agent_rx;
    uvm_byte_array::config_item byte_array_cfg_rx;

    uvm_logic_vector::agent#(LOGIC_WIDTH) m_logic_vector_agent;
    uvm_logic_vector::config_item logic_vector_agent_cfg;

    // Definition of agents, LII agents are used on both sides.
    uvm_lii::agent_rx #(DATA_WIDTH, FAST_SOF, META_WIDTH, SOF_WIDTH) m_lii_agent_rx;
    uvm_lii::config_item lii_cfg_rx;

    config_item m_config;

    //uvm_lii::coverage #(DATA_WIDTH, META_WIDTH) m_cover_rx;

    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);

        if(!uvm_config_db #(config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(get_type_name(), "Unable to get configuration object")
        end

        //m_cover_rx = new("m_cover_rx");
        byte_array_cfg_rx = new;
        lii_cfg_rx = new;
        logic_vector_agent_cfg = new;

        byte_array_cfg_rx.active = m_config.active;

        lii_cfg_rx.active = m_config.active;
        lii_cfg_rx.interface_name = m_config.interface_name;

        logic_vector_agent_cfg.active = m_config.active;

        uvm_config_db #(uvm_byte_array::config_item)::set(this, "m_byte_array_agent_rx", "m_config", byte_array_cfg_rx);
        uvm_config_db #(uvm_lii::config_item)::set(this, "m_lii_agent_rx", "m_config", lii_cfg_rx);
        uvm_config_db #(uvm_logic_vector::config_item)::set(this, "m_logic_vector_agent", "m_config", logic_vector_agent_cfg);

        uvm_byte_array::monitor::type_id::set_inst_override(monitor_byte_array #(DATA_WIDTH, DIC_EN, VERBOSITY, META_WIDTH, SOF_WIDTH)::get_type(),{this.get_full_name(), ".m_byte_array_agent_rx.*"});
        uvm_logic_vector::monitor #(LOGIC_WIDTH)::type_id::set_inst_override(monitor_logic_vector #(DATA_WIDTH, DIC_EN, VERBOSITY, META_WIDTH, LOGIC_WIDTH, SOF_WIDTH)::get_type(), {this.get_full_name(), ".m_logic_vector_agent.*"});
        if (m_config.active == UVM_ACTIVE) begin
            m_sequencer  = uvm_byte_array_lii::sequencer#(LOGIC_WIDTH)::type_id::create("m_sequencer", this);
        end
        m_byte_array_agent_rx = uvm_byte_array::agent::type_id::create("m_byte_array_agent_rx", this);
        m_lii_agent_rx        = uvm_lii::agent_rx #(DATA_WIDTH, FAST_SOF, META_WIDTH, SOF_WIDTH)::type_id::create("m_lii_agent_rx", this);
        m_logic_vector_agent  = uvm_logic_vector::agent#(LOGIC_WIDTH)::type_id::create("m_logic_vector_agent", this);

    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);
        monitor_byte_array #(DATA_WIDTH, DIC_EN, VERBOSITY, META_WIDTH, SOF_WIDTH) m_byte_array_monitor;
        monitor_logic_vector #(DATA_WIDTH, DIC_EN, VERBOSITY, META_WIDTH, LOGIC_WIDTH, SOF_WIDTH) m_logic_vector_monitor;

        uvm_config_db#(uvm_byte_array_lii::sequencer #(LOGIC_WIDTH))::set(this, "m_lii_agent_rx.m_sequencer" , "hi_sqr", m_sequencer);

        $cast(m_byte_array_monitor, m_byte_array_agent_rx.m_monitor);
        m_lii_agent_rx.analysis_port.connect(m_byte_array_monitor.analysis_export);

        $cast(m_logic_vector_monitor, m_logic_vector_agent.m_monitor);
        m_lii_agent_rx.analysis_port.connect(m_logic_vector_monitor.analysis_export);

        //m_lii_agent_rx.analysis_port.connect(m_cover_rx.analysis_export);

        analysis_port_packet = m_byte_array_agent_rx.analysis_port;
        analysis_port_meta   = m_logic_vector_agent.analysis_port;
        if (m_config.active == UVM_ACTIVE) begin
            m_sequencer.m_meta   = m_logic_vector_agent.m_sequencer;
            m_sequencer.m_packet = m_byte_array_agent_rx.m_sequencer;
        end

    endfunction

    virtual task run_phase(uvm_phase phase);

        if (m_config.active == UVM_ACTIVE) begin
            sequence_lib #(DATA_WIDTH, FAST_SOF, DIC_EN, VERBOSITY, META_WIDTH, LOGIC_WIDTH, SOF_WIDTH) seq_lib = uvm_byte_array_lii::sequence_lib #(DATA_WIDTH, FAST_SOF, DIC_EN, VERBOSITY, META_WIDTH, LOGIC_WIDTH, SOF_WIDTH)::type_id::create("sequence_lib");

            if (m_config.type_of_sequence == config_item::RX_MAC) begin
                seq_lib.init_sequence_rx_mac();
            end
            if (m_config.type_of_sequence == config_item::TX_MAC) begin
                seq_lib.init_sequence_tx_mac();
            end
            if (m_config.type_of_sequence == config_item::PCS) begin
                seq_lib.init_sequence_pcs();
            end
            if (m_config.type_of_sequence == config_item::ETH_PHY) begin
                seq_lib.init_sequence_eth_phy();
            end

            seq_lib.min_random_count = 20;
            seq_lib.max_random_count = 100;

            forever begin
                if(!seq_lib.randomize()) `uvm_fatal(this.get_full_name(), "\n\tCannot randomize byte_array_lii rx_seq");
                seq_lib.start(m_lii_agent_rx.m_sequencer);
            end

        end

    endtask

endclass

class env_tx #(int unsigned DATA_WIDTH, logic FAST_SOF, logic DIC_EN, int unsigned VERBOSITY, int unsigned META_WIDTH, int unsigned LOGIC_WIDTH, int unsigned SOF_WIDTH) extends uvm_env;

    `uvm_component_param_utils(uvm_byte_array_lii::env_tx #(DATA_WIDTH, FAST_SOF, DIC_EN, VERBOSITY, META_WIDTH, LOGIC_WIDTH, SOF_WIDTH));

    uvm_analysis_port #(uvm_byte_array::sequence_item) analysis_port_packet;
    uvm_analysis_port #(uvm_logic_vector::sequence_item#(LOGIC_WIDTH)) analysis_port_meta;
    uvm_byte_array_lii::sequencer #(LOGIC_WIDTH) m_sequencer;

    // Definition of agents, high level agents are used on both sides.
    uvm_byte_array::agent m_byte_array_agent_tx;
    uvm_byte_array::config_item byte_array_cfg_tx;

    uvm_logic_vector::agent#(LOGIC_WIDTH) m_logic_vector_agent;
    uvm_logic_vector::config_item logic_vector_agent_cfg;

    // Definition of agents, lII agents are used on both sides.
    uvm_lii::agent_tx #(DATA_WIDTH, FAST_SOF, META_WIDTH, SOF_WIDTH) m_lii_agent_tx;
    uvm_lii::config_item lii_cfg_tx;

    config_item m_config;

    //uvm_lii::coverage #(DATA_WIDTH, META_WIDTH, SOF_WIDTH) m_cover_tx;

    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);

        if(!uvm_config_db #(config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(get_type_name(), "Unable to get configuration object")
        end

        //m_cover_tx = new("m_cover_tx");
        byte_array_cfg_tx = new;
        lii_cfg_tx = new;
        logic_vector_agent_cfg = new;

        byte_array_cfg_tx.active = m_config.active;

        lii_cfg_tx.active = m_config.active;
        lii_cfg_tx.interface_name = m_config.interface_name;

        logic_vector_agent_cfg.active = m_config.active;

        uvm_config_db #(uvm_byte_array::config_item)::set(this, "m_byte_array_agent_tx", "m_config", byte_array_cfg_tx);
        uvm_config_db #(uvm_lii::config_item)::set(this, "m_lii_agent_tx", "m_config", lii_cfg_tx);
        uvm_config_db #(uvm_logic_vector::config_item)::set(this, "m_logic_vector_agent", "m_config", logic_vector_agent_cfg);

        uvm_byte_array::monitor::type_id::set_inst_override(monitor_byte_array #(DATA_WIDTH, DIC_EN, VERBOSITY, META_WIDTH, SOF_WIDTH)::get_type(), {this.get_full_name(), ".m_byte_array_agent_tx.*"});
        uvm_logic_vector::monitor#(LOGIC_WIDTH)::type_id::set_inst_override(monitor_logic_vector #(DATA_WIDTH, DIC_EN, VERBOSITY, META_WIDTH, LOGIC_WIDTH, SOF_WIDTH)::get_type(), {this.get_full_name(), ".m_logic_vector_agent.*"});

        if (m_config.active == UVM_ACTIVE) begin
            m_sequencer  = uvm_byte_array_lii::sequencer#(LOGIC_WIDTH)::type_id::create("m_sequencer", this);
        end
        m_byte_array_agent_tx    = uvm_byte_array::agent::type_id::create("m_byte_array_agent_tx", this);
        m_lii_agent_tx        = uvm_lii::agent_tx #(DATA_WIDTH, FAST_SOF, META_WIDTH, SOF_WIDTH)::type_id::create("m_lii_agent_tx", this);
        m_logic_vector_agent = uvm_logic_vector::agent#(LOGIC_WIDTH)::type_id::create("m_logic_vector_agent", this);

    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);
        monitor_byte_array #(DATA_WIDTH, DIC_EN, VERBOSITY, META_WIDTH, SOF_WIDTH) m_byte_array_monitor;
        monitor_logic_vector #(DATA_WIDTH, DIC_EN, VERBOSITY, META_WIDTH, LOGIC_WIDTH, SOF_WIDTH) m_logic_vector_monitor;

        uvm_config_db#(uvm_byte_array_lii::sequencer #(LOGIC_WIDTH))::set(this, "m_lii_agent_tx.m_sequencer" , "hi_sqr", m_sequencer);

        $cast(m_byte_array_monitor, m_byte_array_agent_tx.m_monitor);
        m_lii_agent_tx.analysis_port.connect(m_byte_array_monitor.analysis_export);

        $cast(m_logic_vector_monitor, m_logic_vector_agent.m_monitor);
        m_lii_agent_tx.analysis_port.connect(m_logic_vector_monitor.analysis_export);

        //m_lii_agent_tx.analysis_port.connect(m_cover_tx.analysis_export);

        analysis_port_packet = m_byte_array_agent_tx.analysis_port;
        analysis_port_meta   = m_logic_vector_agent.analysis_port;
        if (m_config.active == UVM_ACTIVE) begin
            m_sequencer.m_packet = m_byte_array_agent_tx.m_sequencer;
        end

    endfunction

    virtual task run_phase(uvm_phase phase);

        if (m_config.active == UVM_ACTIVE) begin
            sequence_lib #(DATA_WIDTH, FAST_SOF, DIC_EN, VERBOSITY, META_WIDTH, LOGIC_WIDTH, SOF_WIDTH) seq_lib = uvm_byte_array_lii::sequence_lib #(DATA_WIDTH, FAST_SOF, DIC_EN, VERBOSITY, META_WIDTH, LOGIC_WIDTH, SOF_WIDTH)::type_id::create("sequence_lib");

            if (m_config.type_of_sequence == config_item::RX_MAC || m_config.type_of_sequence == config_item::TX_MAC) begin
                seq_lib.init_sequence_mac_rdy();
            end

            if (m_config.type_of_sequence == config_item::PCS) begin
                seq_lib.init_sequence_pcs_rdy();
            end

            forever begin
                if(!seq_lib.randomize()) `uvm_fatal(this.get_full_name(), "\n\tCannot randomize byte_array_lii rx_seq");
                seq_lib.start(m_lii_agent_tx.m_sequencer);
            end

        end

    endtask

endclass

class env_eth_phy_rx #(int unsigned DATA_WIDTH, logic FAST_SOF, logic DIC_EN, int unsigned VERBOSITY, int unsigned META_WIDTH, int unsigned LOGIC_WIDTH, MEAS, int unsigned SOF_WIDTH) extends uvm_env;

    `uvm_component_param_utils(uvm_byte_array_lii::env_eth_phy_rx #(DATA_WIDTH, FAST_SOF, DIC_EN, VERBOSITY, META_WIDTH, LOGIC_WIDTH, MEAS, SOF_WIDTH));

    uvm_analysis_port #(uvm_byte_array::sequence_item) analysis_port_packet;
    uvm_analysis_port #(uvm_logic_vector::sequence_item#(LOGIC_WIDTH)) analysis_port_meta;
    uvm_byte_array_lii::sequencer #(LOGIC_WIDTH) m_sequencer;

    // Definition of agents, high level agents are used on both sides.
    uvm_byte_array::agent m_byte_array_agent_rx;
    uvm_byte_array::config_item byte_array_cfg_rx;

    uvm_logic_vector::agent#(LOGIC_WIDTH) m_logic_vector_agent;
    uvm_logic_vector::config_item logic_vector_agent_cfg;

    // Definition of agents, LII agents are used on both sides.
    uvm_lii::agent_rx_eth_phy #(DATA_WIDTH, FAST_SOF, META_WIDTH, MEAS, SOF_WIDTH) m_lii_agent_rx;
    uvm_lii::config_item lii_cfg_rx;

    config_item m_config;

    //uvm_lii::coverage #(DATA_WIDTH, META_WIDTH) m_cover_rx;

    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);

        if(!uvm_config_db #(config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(get_type_name(), "Unable to get configuration object")
        end

        //m_cover_rx = new("m_cover_rx");
        byte_array_cfg_rx = new;
        lii_cfg_rx = new;
        logic_vector_agent_cfg = new;

        byte_array_cfg_rx.active = m_config.active;

        lii_cfg_rx.active = m_config.active;
        lii_cfg_rx.interface_name = m_config.interface_name;

        logic_vector_agent_cfg.active = m_config.active;

        uvm_config_db #(uvm_byte_array::config_item)::set(this, "m_byte_array_agent_rx", "m_config", byte_array_cfg_rx);
        uvm_config_db #(uvm_lii::config_item)::set(this, "m_lii_agent_rx", "m_config", lii_cfg_rx);
        uvm_config_db #(uvm_logic_vector::config_item)::set(this, "m_logic_vector_agent", "m_config", logic_vector_agent_cfg);

        uvm_byte_array::monitor::type_id::set_inst_override(monitor_byte_array #(DATA_WIDTH, DIC_EN, VERBOSITY, META_WIDTH, SOF_WIDTH)::get_type(),{this.get_full_name(), ".m_byte_array_agent_rx.*"});
        uvm_logic_vector::monitor #(LOGIC_WIDTH)::type_id::set_inst_override(monitor_logic_vector #(DATA_WIDTH, DIC_EN, VERBOSITY, META_WIDTH, LOGIC_WIDTH, SOF_WIDTH)::get_type(), {this.get_full_name(), ".m_logic_vector_agent.*"});
        if (m_config.active == UVM_ACTIVE) begin
            m_sequencer  = uvm_byte_array_lii::sequencer#(LOGIC_WIDTH)::type_id::create("m_sequencer", this);
        end
        m_byte_array_agent_rx = uvm_byte_array::agent::type_id::create("m_byte_array_agent_rx", this);
        m_lii_agent_rx        = uvm_lii::agent_rx_eth_phy #(DATA_WIDTH, FAST_SOF, META_WIDTH, MEAS, SOF_WIDTH)::type_id::create("m_lii_agent_rx", this);
        m_logic_vector_agent  = uvm_logic_vector::agent#(LOGIC_WIDTH)::type_id::create("m_logic_vector_agent", this);

    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);
        monitor_byte_array #(DATA_WIDTH, DIC_EN, VERBOSITY, META_WIDTH, SOF_WIDTH) m_byte_array_monitor;
        monitor_logic_vector #(DATA_WIDTH, DIC_EN, VERBOSITY, META_WIDTH, LOGIC_WIDTH, SOF_WIDTH) m_logic_vector_monitor;

        uvm_config_db#(uvm_byte_array_lii::sequencer #(LOGIC_WIDTH))::set(this, "m_lii_agent_rx.m_sequencer" , "hi_sqr", m_sequencer);

        $cast(m_byte_array_monitor, m_byte_array_agent_rx.m_monitor);
        m_lii_agent_rx.analysis_port.connect(m_byte_array_monitor.analysis_export);

        $cast(m_logic_vector_monitor, m_logic_vector_agent.m_monitor);
        m_lii_agent_rx.analysis_port.connect(m_logic_vector_monitor.analysis_export);

        //m_lii_agent_rx.analysis_port.connect(m_cover_rx.analysis_export);

        analysis_port_packet = m_byte_array_agent_rx.analysis_port;
        analysis_port_meta   = m_logic_vector_agent.analysis_port;
        if (m_config.active == UVM_ACTIVE) begin
            m_sequencer.m_meta   = m_logic_vector_agent.m_sequencer;
            m_sequencer.m_packet = m_byte_array_agent_rx.m_sequencer;
        end

    endfunction

    virtual task run_phase(uvm_phase phase);

        if (m_config.active == UVM_ACTIVE) begin
            sequence_lib #(DATA_WIDTH, FAST_SOF, DIC_EN, VERBOSITY, META_WIDTH, LOGIC_WIDTH, SOF_WIDTH) seq_lib = uvm_byte_array_lii::sequence_lib #(DATA_WIDTH, FAST_SOF, DIC_EN, VERBOSITY, META_WIDTH, LOGIC_WIDTH, SOF_WIDTH)::type_id::create("sequence_lib");

            if (m_config.type_of_sequence == config_item::RX_MAC) begin
                seq_lib.init_sequence_rx_mac();
            end
            if (m_config.type_of_sequence == config_item::TX_MAC) begin
                seq_lib.init_sequence_tx_mac();
            end
            if (m_config.type_of_sequence == config_item::ETH_PHY) begin
                seq_lib.init_sequence_eth_phy();
            end
            if (m_config.type_of_sequence == config_item::PCS) begin
                seq_lib.init_sequence_pcs();
            end

            forever begin
                if(!seq_lib.randomize()) `uvm_fatal(this.get_full_name(), "\n\tCannot randomize byte_array_lii rx_seq");
                seq_lib.start(m_lii_agent_rx.m_sequencer);
            end

        end

    endtask

endclass

`endif
