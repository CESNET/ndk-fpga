/*
 * file       : env.sv
 * description: rx environment
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * Copyright (C) 2021 CESNET z. s. p. o.
*/

`ifndef RX_ENV_SV
`define RX_ENV_SV

class env #(int unsigned DATA_WIDTH) extends uvm_env;

    `uvm_component_param_utils(uvm_byte_array_pma::env #(DATA_WIDTH));

    // Definition of agents, high level agents are used on both sides.
    uvm_byte_array::agent m_byte_array_agent;
    uvm_byte_array::config_item m_byte_array_config;

    // Definition of agents, PMA agents are used on both sides.
    uvm_pma::agent #(DATA_WIDTH) m_pma_agent;
    uvm_pma::config_item m_pma_config;
    uvm_byte_array_pma::sequencer m_sequencer;

    config_item m_config;

    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);

        if(!uvm_config_db #(config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(this.get_full_name(), "Unable to get configuration object")
        end

        m_byte_array_config = new;
        m_pma_config        = new;

        m_byte_array_config.active  = m_config.active;

        m_pma_config.active         = m_config.active;
        m_pma_config.interface_name = m_config.interface_name;

        uvm_config_db #(uvm_byte_array::config_item)::set(this, "m_byte_array_agent", "m_config", m_byte_array_config);
        uvm_config_db #(uvm_pma::config_item)::set(this, "m_pma_agent", "m_config", m_pma_config);

        uvm_byte_array::monitor::type_id::set_inst_override(monitor #(DATA_WIDTH)::get_type(), {this.get_full_name(), ".m_byte_array_agent.*"});

        if (m_config.active == UVM_ACTIVE) begin
            m_sequencer  = uvm_byte_array_pma::sequencer::type_id::create("m_sequencer", this);
        end

        m_byte_array_agent = uvm_byte_array::agent::type_id::create("m_byte_array_agent", this);
        m_pma_agent        = uvm_pma::agent #(DATA_WIDTH)::type_id::create("m_pma_agent", this);

    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);
        monitor #(DATA_WIDTH) env_monitor;

        uvm_config_db#(uvm_byte_array_pma::sequencer)::set(this, "m_pma_agent.m_sequencer" , "hi_sqr", m_sequencer);

        $cast(env_monitor, m_byte_array_agent.m_monitor);
        m_pma_agent.analysis_port.connect(env_monitor.analysis_export);
        if (m_config.active == UVM_ACTIVE) begin
            m_sequencer.m_packet = m_byte_array_agent.m_sequencer;
        end

    endfunction

    virtual task run_phase(uvm_phase phase);

        if (m_config.active == UVM_ACTIVE) begin
            sequence_lib #(DATA_WIDTH) seq_lib = uvm_byte_array_pma::sequence_lib #(DATA_WIDTH)::type_id::create("sequence_lib");
            seq_lib.min_random_count = 1;
            seq_lib.max_random_count = 50;
            seq_lib.init_sequence_rx_pcs();

            forever begin
                if(!seq_lib.randomize()) `uvm_fatal(this.get_full_name(), "\n\tCannot randomize byte_array_lii rx_seq");
                seq_lib.start(m_pma_agent.m_sequencer);
            end
        end

    endtask

endclass

`endif
