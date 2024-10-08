// env.sv: Verification environment
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class env #(MVB_ITEMS, MVB_ITEM_WIDTH, RX_STREAMS) extends uvm_env;
    `uvm_component_param_utils(uvm_mvb_merge_streams_ordered::env #(MVB_ITEMS, MVB_ITEM_WIDTH, RX_STREAMS))

    // Environments
    uvm_reset::agent                                                          m_reset_agent;
    uvm_logic_vector_mvb::env_rx #(MVB_ITEMS, MVB_ITEM_WIDTH)                 m_rx_mvb_env [RX_STREAMS -1 : 0];
    uvm_logic_vector_mvb::env_rx #(MVB_ITEMS*RX_STREAMS, $clog2(RX_STREAMS))  m_rx_sel_mvb_env;
    uvm_logic_vector_mvb::env_tx #(MVB_ITEMS*RX_STREAMS, MVB_ITEM_WIDTH)      m_tx_mvb_env;

    // Configuration objects
    uvm_reset           ::config_item  m_reset_config;
    uvm_logic_vector_mvb::config_item  m_rx_mvb_config [RX_STREAMS -1 : 0];
    uvm_logic_vector_mvb::config_item  m_rx_sel_mvb_config;
    uvm_logic_vector_mvb::config_item  m_tx_mvb_config;

    // Scoreboard
    uvm_mvb_merge_streams_ordered::scoreboard #(MVB_ITEM_WIDTH, RX_STREAMS) m_scbrd;
    // Virtual sequencer
    uvm_mvb_merge_streams_ordered::virt_sequencer #(MVB_ITEMS, MVB_ITEM_WIDTH, RX_STREAMS) m_virt_sqcr;

    // Coverages
    uvm_mvb::coverage #(MVB_ITEMS, MVB_ITEM_WIDTH)                 m_rx_mvb_cover;
    uvm_mvb::coverage #(MVB_ITEMS*RX_STREAMS, $clog2(RX_STREAMS))  m_rx_sel_mvb_cover;
    uvm_mvb::coverage #(MVB_ITEMS*RX_STREAMS, MVB_ITEM_WIDTH)      m_tx_mvb_cover;

    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);

        // Configuration of the reset
        m_reset_config                = new;
        m_reset_config.active         = UVM_ACTIVE;
        m_reset_config.interface_name = "reset_vif";
        uvm_config_db #(uvm_reset::config_item)::set(this, "m_reset_agent", "m_config", m_reset_config);
        // Creation of the reset
        m_reset_agent = uvm_reset::agent::type_id::create("m_reset_agent", this);

        for (int port = 0; port < RX_STREAMS; port++) begin
            // Configuration of the RX MVB environment
            m_rx_mvb_config[port]                 = new;
            m_rx_mvb_config[port].active          = UVM_ACTIVE;
            m_rx_mvb_config[port].interface_name  = $sformatf("rx_mvb_vif_%0d", port);
            uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, $sformatf("m_rx_mvb_env_%0d", port), "m_config", m_rx_mvb_config[port]);
            // Creation of the RX_MVB environment
            m_rx_mvb_env[port]      = uvm_logic_vector_mvb::env_rx #(MVB_ITEMS, MVB_ITEM_WIDTH)::type_id::create($sformatf("m_rx_mvb_env_%0d", port), this);
        end

        // Configuration of the RX SEL MVB environment
        m_rx_sel_mvb_config                 = new;
        m_rx_sel_mvb_config.active          = UVM_ACTIVE;
        m_rx_sel_mvb_config.interface_name  = "rx_sel_mvb_vif";
        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "m_rx_sel_mvb_env", "m_config", m_rx_sel_mvb_config);
        // Creation of the RX SEL MVB environment
        m_rx_sel_mvb_env  = uvm_logic_vector_mvb::env_rx #(MVB_ITEMS*RX_STREAMS, $clog2(RX_STREAMS))::type_id::create("m_rx_sel_mvb_env", this);

        // Configuration of the TX MVB environment
        m_tx_mvb_config                     = new;
        m_tx_mvb_config.active              = UVM_ACTIVE;
        m_tx_mvb_config.interface_name      = "tx_mvb_vif";
        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "m_tx_mvb_env", "m_config", m_tx_mvb_config);
        // Creation of TX MVB environment
        m_tx_mvb_env      = uvm_logic_vector_mvb::env_tx #(MVB_ITEMS*RX_STREAMS,MVB_ITEM_WIDTH)::type_id::create("m_tx_mvb_env", this);

        // Creation of the coverages
        m_rx_mvb_cover     = new("m_rx_mvb_cover");
        m_rx_sel_mvb_cover = new("m_rx_sel_mvb_cover");
        m_tx_mvb_cover     = new("m_tx_mvb_cover");

        // Creation of the scoreboard
        m_scbrd = scoreboard #(MVB_ITEM_WIDTH, RX_STREAMS)::type_id::create("m_scbrd", this);
        // Creation of the virtual sequencer
        m_virt_sqcr = uvm_mvb_merge_streams_ordered::virt_sequencer #(MVB_ITEMS, MVB_ITEM_WIDTH, RX_STREAMS)::type_id::create("r", this);
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);

        // Connection of the reset
        for (int port = 0; port < RX_STREAMS; port++) begin
            m_reset_agent.sync_connect(m_rx_mvb_env[port].reset_sync);
        end
        m_reset_agent    .sync_connect(m_rx_sel_mvb_env  .reset_sync);
        m_reset_agent    .sync_connect(m_tx_mvb_env      .reset_sync);

        // RX environments connection
        for (int port = 0; port < RX_STREAMS; port++) begin
            m_rx_mvb_env[port].analysis_port.connect(m_scbrd.rx_mvb_analysis_imp[port]);
        end
        m_rx_sel_mvb_env      .analysis_port.connect(m_scbrd.rx_sel_mvb_analysis_imp);

        // TX environment connection
        m_tx_mvb_env.analysis_port.connect(m_scbrd.tx_mvb_analysis_exp);

        // Connections of the coverages
        for (int port = 0; port < RX_STREAMS; port++) begin
            m_rx_mvb_env[port].m_mvb_agent.analysis_port.connect(m_rx_mvb_cover    .analysis_export);
        end
        m_rx_sel_mvb_env      .m_mvb_agent.analysis_port.connect(m_rx_sel_mvb_cover.analysis_export);
        m_tx_mvb_env          .m_mvb_agent.analysis_port.connect(m_tx_mvb_cover    .analysis_export);

        // Passing the sequencers to the virtual sequencer
        m_virt_sqcr.m_reset_sqcr            = m_reset_agent     .m_sequencer;
        for (int port = 0; port < RX_STREAMS; port++) begin
            m_virt_sqcr.m_rx_mvb_sqcr[port] = m_rx_mvb_env[port].m_sequencer;
        end
        m_virt_sqcr.m_rx_sel_mvb_sqcr       = m_rx_sel_mvb_env  .m_sequencer;
        m_virt_sqcr.m_tx_mvb_sqcr           = m_tx_mvb_env      .m_sequencer;
    endfunction
endclass
