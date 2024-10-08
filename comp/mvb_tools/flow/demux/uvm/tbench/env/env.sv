// env.sv: Verification environment
// Copyright (C) 2023-2024 CESNET z. s. p. o.
// Author: Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
//         Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class env #(ITEMS, ITEM_WIDTH, TX_PORTS) extends uvm_env;
    `uvm_component_param_utils(uvm_mvb_demux::env #(ITEMS, ITEM_WIDTH, TX_PORTS));

    uvm_reset::agent                                                      m_reset_agent;
    uvm_logic_vector_mvb::env_rx #(ITEMS, ITEM_WIDTH + $clog2(TX_PORTS))  m_rx_mvb_env;
    uvm_logic_vector_mvb::env_tx #(ITEMS, ITEM_WIDTH)                     m_tx_mvb_env [TX_PORTS -1 : 0];

    uvm_reset::config_item             m_reset_config;
    uvm_logic_vector_mvb::config_item  m_rx_mvb_config;
    uvm_logic_vector_mvb::config_item  m_tx_mvb_config [TX_PORTS -1 : 0];

    uvm_mvb_demux::virt_sequencer #(ITEM_WIDTH, TX_PORTS) m_virt_sqcr;

    scoreboard #(ITEM_WIDTH, TX_PORTS) m_scoreboard;

    uvm_mvb::coverage #(ITEMS, ITEM_WIDTH + $clog2(TX_PORTS))  m_rx_mvb_cover;
    uvm_mvb::coverage #(ITEMS, ITEM_WIDTH)                     m_tx_mvb_cover;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Initialize components of the environment.
    function void build_phase(uvm_phase phase);
        m_reset_config                = new;
        m_reset_config.active         = UVM_ACTIVE;
        m_reset_config.interface_name = "reset_vif";
        uvm_config_db #(uvm_reset::config_item)::set(this, "m_reset_agent", "m_config", m_reset_config);
        m_reset_agent = uvm_reset::agent::type_id::create("m_reset_agent", this);

        m_rx_mvb_config                = new;
        m_rx_mvb_config.active         = UVM_ACTIVE;
        m_rx_mvb_config.interface_name = "rx_mvb_vif";
        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "m_rx_mvb_env", "m_config", m_rx_mvb_config);
        m_rx_mvb_env = uvm_logic_vector_mvb::env_rx #(ITEMS, ITEM_WIDTH + $clog2(TX_PORTS))::type_id::create("m_rx_mvb_env", this);

        for (int i = 0; i < TX_PORTS; i++) begin
            m_tx_mvb_config[i]                = new;
            m_tx_mvb_config[i].active         = UVM_ACTIVE;
            m_tx_mvb_config[i].interface_name = $sformatf("tx_mvb_vif_%0d", i);
            uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, $sformatf("m_tx_mvb_env_%0d", i), "m_config" , m_tx_mvb_config[i]);
            m_tx_mvb_env[i] = uvm_logic_vector_mvb::env_tx #(ITEMS, ITEM_WIDTH)::type_id::create($sformatf("m_tx_mvb_env_%0d", i), this);
        end

        m_virt_sqcr = uvm_mvb_demux::virt_sequencer#(ITEM_WIDTH, TX_PORTS)::type_id::create("m_virt_sqcr",this);

        m_scoreboard  = scoreboard #(ITEM_WIDTH, TX_PORTS)::type_id::create("m_scoreboard", this);

        m_rx_mvb_cover = uvm_mvb::coverage #(ITEMS, ITEM_WIDTH + $clog2(TX_PORTS))::type_id::create("m_rx_mvb_cover", this);
        m_tx_mvb_cover = uvm_mvb::coverage #(ITEMS, ITEM_WIDTH)::type_id::create("m_tx_mvb_cover", this);
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);

        // Connect reset
        m_reset_agent     .sync_connect(m_rx_mvb_env.reset_sync);
        for (int i = 0; i < TX_PORTS; i++) begin
            m_reset_agent .sync_connect(m_tx_mvb_env[i].reset_sync);
        end

        // Connect ports
        m_rx_mvb_env.analysis_port        .connect(m_scoreboard.rx_mvb_analysis_imp);
        for (int i = 0; i < TX_PORTS; i++) begin
            m_tx_mvb_env[i].analysis_port .connect(m_scoreboard.tx_mvb_analysis_exp[i]);
        end

        // Connect coverages
        m_rx_mvb_env.m_mvb_agent        .analysis_port.connect(m_rx_mvb_cover.analysis_export);
        for (int i = 0; i < TX_PORTS; i++) begin
            m_tx_mvb_env[i].m_mvb_agent .analysis_port.connect(m_tx_mvb_cover.analysis_export);
        end

        // Connect sequencers to the virtual sequencer
        m_virt_sqcr.m_reset_sqcr        = m_reset_agent.m_sequencer;
        m_virt_sqcr.m_logic_vector_sqcr = m_rx_mvb_env.m_sequencer;
    endfunction
endclass
