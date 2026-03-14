//-- env.sv: Mfb environment
//-- Copyright (C) 2026 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// Definition of axi environment
class env_rx #(int unsigned ITEMS,  int unsigned ITEM_WIDTH) extends uvm_env;
    `uvm_component_param_utils(uvm_logic_vector_array_axi::env_rx #(ITEMS, ITEM_WIDTH));

    localparam  TUSER_WIDTH = 0;

    // ------------------------------------------------------------------------
    // Definition of agents
    uvm_logic_vector_array::sequencer #(ITEM_WIDTH) m_sequencer;
    uvm_analysis_port #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)) analysis_port;
    uvm_reset::sync_cbs            reset_sync;


    protected uvm_logic_vector_array::agent#(ITEM_WIDTH) m_logic_vector_array_agent;
    protected uvm_axi::agent_rx #(ITEMS, ITEM_WIDTH, TUSER_WIDTH) m_axi_agent;

    protected config_item m_config;

    // Constructor of environment.
    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);
        uvm_logic_vector_array::config_item logic_vector_array_agent_cfg;
        uvm_axi::config_item axi_agent_cfg;

        if(!uvm_config_db #(config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(get_type_name(), "Unable to get configuration object")
        end

        logic_vector_array_agent_cfg = new;
        logic_vector_array_agent_cfg.active = m_config.active;
        uvm_config_db #(uvm_logic_vector_array::config_item)::set(
            this, "m_logic_vector_array_agent", "m_config", logic_vector_array_agent_cfg
        );
        uvm_logic_vector_array::monitor #(ITEM_WIDTH)::type_id::set_inst_override(
            monitor_axi_lva #(ITEMS, ITEM_WIDTH)::get_type(),
            "m_logic_vector_array_agent.*", this
        );
        m_logic_vector_array_agent = uvm_logic_vector_array::agent#(ITEM_WIDTH)::type_id::create(
            "m_logic_vector_array_agent", this
        );


        axi_agent_cfg = new;
        axi_agent_cfg.active = m_config.active;
        axi_agent_cfg.interface_name = m_config.interface_name;
        uvm_config_db #(uvm_axi::config_item)::set(this, "m_axi_agent", "m_config", axi_agent_cfg);
        m_axi_agent        = uvm_axi::agent_rx #(ITEMS, ITEM_WIDTH, TUSER_WIDTH)::type_id::create("m_axi_agent", this);

        if (m_config.active == UVM_ACTIVE) begin
            m_sequencer =uvm_logic_vector_array::sequencer #(ITEM_WIDTH)::type_id::create("m_sequencer", this);
        end else begin
            m_sequencer = null;
        end

        reset_sync = new();
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);
        monitor_axi_lva #(ITEMS, ITEM_WIDTH) m_byte_arr_monitor;

        $cast(m_byte_arr_monitor, m_logic_vector_array_agent.m_monitor);
        m_axi_agent.analysis_port.connect(m_byte_arr_monitor.analysis_export);
        analysis_port = m_byte_arr_monitor.analysis_port;
        reset_sync.push_back(m_byte_arr_monitor.reset_sync);

        if (m_config.active == UVM_ACTIVE) begin
            m_sequencer = m_logic_vector_array_agent.m_sequencer;
            reset_sync.push_back(m_axi_agent.m_sequencer.reset_sync);
            uvm_config_db #(uvm_logic_vector_array::sequencer #(ITEM_WIDTH))::set(
                this, "m_axi_agent.m_sequencer", "hl_sqr", m_logic_vector_array_agent.m_sequencer
            );
        end
    endfunction

    virtual task run_phase(uvm_phase phase);
        if (m_config.active == UVM_ACTIVE) begin
            uvm_common::sequence_library#(config_sequence, uvm_axi::sequence_item #(ITEMS, ITEM_WIDTH, 0)) axi_seq;

            axi_seq = sequence_lib_rx#(ITEMS, ITEM_WIDTH)::type_id::create("axi_seq", this);

            axi_seq.min_random_count = 20;
            axi_seq.max_random_count = 100;
            axi_seq.init_sequence(m_config.seq_cfg);

            forever begin
                int verbosity;

                verbosity = this.get_report_verbosity_level(UVM_INFO, "axi_seq");
                m_axi_agent.m_sequencer.set_report_verbosity_level(verbosity >= 300 ? verbosity - 300 : 0);

                assert(!axi_seq.randomize()) else begin
                    `uvm_fatal(this.get_full_name(), "\n\tCannot randomize logic_vector_array_axi rx_seq");
                end
                axi_seq.start(m_axi_agent.m_sequencer);
            end
        end
    endtask

endclass


class env_tx #(int unsigned ITEMS, int unsigned ITEM_WIDTH) extends uvm_env;
    `uvm_component_param_utils(uvm_logic_vector_array_axi::env_tx #(ITEMS, ITEM_WIDTH));

    //localparam  ITEM_WIDTH = 32;

    //Access component
    uvm_analysis_port #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)) analysis_port;
    uvm_reset::sync_cbs                                               reset_sync;

    // ------------------------------------------------------------------------
    // Definition of agents
    protected uvm_logic_vector_array::agent#(ITEM_WIDTH) m_logic_vector_array_agent;
    protected uvm_axi::agent_tx #(ITEMS, ITEM_WIDTH, 0) m_axi_agent;

    protected config_item m_config;

    // Constructor of environment.
    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);
        uvm_logic_vector_array::config_item logic_vector_array_agent_cfg;
        uvm_axi::config_item axi_agent_cfg;

        if(!uvm_config_db #(config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(get_type_name(), "Unable to get configuration object")
        end

        logic_vector_array_agent_cfg = new;
        logic_vector_array_agent_cfg.active = m_config.active;
        uvm_config_db #(uvm_logic_vector_array::config_item)::set(
            this, "m_logic_vector_array_agent", "m_config", logic_vector_array_agent_cfg
        );
        m_logic_vector_array_agent = uvm_logic_vector_array::agent#(ITEM_WIDTH)::type_id::create(
            "m_logic_vector_array_agent", this
        );

        axi_agent_cfg = new;
        axi_agent_cfg.active = m_config.active;
        axi_agent_cfg.interface_name = m_config.interface_name;
        uvm_config_db #(uvm_axi::config_item)::set(this, "m_axi_agent", "m_config", axi_agent_cfg);
        uvm_logic_vector_array::monitor#(ITEM_WIDTH)::type_id::set_inst_override(
            monitor_axi_lva #(ITEMS, ITEM_WIDTH)::get_type(),
            "m_logic_vector_array_agent.*", this
        );
        m_axi_agent  = uvm_axi::agent_tx #(ITEMS, ITEM_WIDTH, 0)::type_id::create("m_axi_agent", this);

        reset_sync = new();
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);

        monitor_axi_lva #(ITEMS, ITEM_WIDTH)   m_byte_arr_monitor;

        $cast(m_byte_arr_monitor, m_logic_vector_array_agent.m_monitor);
        m_axi_agent.analysis_port.connect(m_byte_arr_monitor.analysis_export);
        analysis_port = m_byte_arr_monitor.analysis_port;
        reset_sync.push_back(m_byte_arr_monitor.reset_sync);
    endfunction

    task run_phase(uvm_phase phase);
        uvm_axi::sequence_lib_tx#(ITEMS, ITEM_WIDTH, 0) axi_seq;


        if (m_config.active == UVM_ACTIVE) begin
            axi_seq = uvm_axi::sequence_lib_tx#(ITEMS, ITEM_WIDTH, 0)::type_id::create("axi_seq", this);
            axi_seq.init_sequence();
            axi_seq.min_random_count =  100;
            axi_seq.max_random_count = 2000;

            forever begin
                assert(axi_seq.randomize()) else begin
                    `uvm_fatal(this.get_full_name(), "\n\tCannot randomize TX sequence\n");
                end
                axi_seq.start(m_axi_agent.m_sequencer);
            end
        end
    endtask
endclass

