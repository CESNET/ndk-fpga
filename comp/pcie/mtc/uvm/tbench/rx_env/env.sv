//-- env.sv
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class env #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, DEVICE, ENDPOINT_TYPE) extends uvm_env;
    `uvm_component_param_utils(uvm_pcie_cq::env #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, DEVICE, ENDPOINT_TYPE));

    localparam CQ_MFB_META_WIDTH = sv_pcie_meta_pack::PCIE_CQ_META_WIDTH;

    //top sequencer
    //sequencer             m_sequencer;
    driver#(MFB_ITEM_WIDTH, DEVICE, ENDPOINT_TYPE) m_driver;

    //toplevel
    uvm_pcie_hdr::agent                            m_pcie_hdr_agent;
    //low level
    uvm_logic_vector_array_mfb::env_rx #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, sv_pcie_meta_pack::PCIE_CQ_META_WIDTH) m_env_rx;
    //implement later
    uvm_reset::sync_cbs reset_sync;
    //configuration
    config_item m_config;

    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);
        uvm_pcie_hdr::config_item               m_pcie_hdr_agent_cfg;
        uvm_logic_vector_array_mfb::config_item m_env_rx_cfg;

        if(!uvm_config_db #(config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(get_type_name(), "Unable to get configuration object")
        end

        //TOP level agent
        m_pcie_hdr_agent_cfg                  = new();
        m_pcie_hdr_agent_cfg.active           = m_config.active;

        uvm_config_db #(uvm_pcie_hdr::config_item)::set(this, "m_pcie_hdr_agent", "m_config", m_pcie_hdr_agent_cfg);
        m_pcie_hdr_agent           = uvm_pcie_hdr::agent::type_id::create("m_pcie_hdr_agent", this);

        //LOW level agent
        m_env_rx_cfg                = new();
        m_env_rx_cfg.active         = m_config.active;
        m_env_rx_cfg.interface_name = m_config.interface_name;
        m_env_rx_cfg.meta_behav     = uvm_logic_vector_array_mfb::config_item::META_SOF;
        uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, "m_env_rx", "m_config", m_env_rx_cfg);
        m_env_rx = uvm_logic_vector_array_mfb::env_rx #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, sv_pcie_meta_pack::PCIE_CQ_META_WIDTH)::type_id::create("m_env_rx", this);

        if (m_config.active == UVM_ACTIVE) begin
            m_driver    = driver#(MFB_ITEM_WIDTH, DEVICE, ENDPOINT_TYPE)::type_id::create("m_driver", this);
        end

        reset_sync = new();
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);
        if (m_config.active == UVM_ACTIVE) begin
            m_driver.seq_item_port_pcie_hdr.connect(m_pcie_hdr_agent.m_sequencer.seq_item_export);
        end

        reset_sync.push_back(m_env_rx.reset_sync);
    endfunction

    virtual task run_phase(uvm_phase phase);
        if (m_config.active == UVM_ACTIVE) begin
            uvm_pcie_cq::logic_vector_sequence#(sv_pcie_meta_pack::PCIE_CQ_META_WIDTH, DEVICE, ENDPOINT_TYPE)       logic_vector_seq;
            uvm_pcie_cq::logic_vector_array_sequence#(MFB_ITEM_WIDTH, DEVICE, ENDPOINT_TYPE) logic_vector_array_seq;

            logic_vector_seq                 = uvm_pcie_cq::logic_vector_sequence#(sv_pcie_meta_pack::PCIE_CQ_META_WIDTH, DEVICE, ENDPOINT_TYPE)::type_id::create("logic_vector_seq", this);
            logic_vector_array_seq           = uvm_pcie_cq::logic_vector_array_sequence #(MFB_ITEM_WIDTH, DEVICE, ENDPOINT_TYPE)::type_id::create("logic_vector_array_seq", this);
            logic_vector_seq.tr_export       = m_driver.logic_vector_export;
            logic_vector_array_seq.tr_export = m_driver.pcie_hdr_rw_export;
            logic_vector_seq.randomize();
            logic_vector_array_seq.randomize();

            fork
                logic_vector_seq.start(m_env_rx.m_sequencer.m_meta);
                logic_vector_array_seq.start(m_env_rx.m_sequencer.m_data);
            join
        end
    endtask
endclass

