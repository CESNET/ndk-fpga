// env.sv: Verification environment
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class env #(int unsigned MVB_ITEMS, int unsigned MVB_ITEM_WIDTH, int unsigned RX_STREAMS) extends uvm_env;
    `uvm_component_param_utils(uvm_mvb_merge_streams::env #(MVB_ITEMS, MVB_ITEM_WIDTH, RX_STREAMS))

    // Reset environment
    uvm_reset::agent m_reset;

    // RX environments
    uvm_logic_vector_mvb::env_rx #(MVB_ITEMS, MVB_ITEM_WIDTH) m_env_rx_mvb[RX_STREAMS];

    // TX environment
    uvm_logic_vector_mvb::env_tx #(MVB_ITEMS, MVB_ITEM_WIDTH) m_env_tx_mvb;

    // Coverage models
    hl_coverage_model #(MVB_ITEM_WIDTH, RX_STREAMS)            m_hl_coverage_model;
    ll_coverage_model #(MVB_ITEMS, MVB_ITEM_WIDTH, RX_STREAMS) m_ll_coverage_model;
    uvm_mvb::coverage #(MVB_ITEMS, MVB_ITEM_WIDTH)             m_coverage_rx_mvb[RX_STREAMS];
    uvm_mvb::coverage #(MVB_ITEMS, MVB_ITEM_WIDTH)             m_coverage_tx_mvb;

    // Scoreboard
    scoreboard #(MVB_ITEM_WIDTH, RX_STREAMS) m_scoreboard;
    // Virtual sequencer
    virtual_sequencer #(MVB_ITEMS, MVB_ITEM_WIDTH, RX_STREAMS) m_virtual_sequencer;

    // Constructor
    function new(string name = "env", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        uvm_reset::config_item            m_config_reset;
        uvm_logic_vector_mvb::config_item m_config_rx_mvb[RX_STREAMS];
        uvm_logic_vector_mvb::config_item m_config_tx_mvb;

        super.build_phase(phase);

        // ------------------------- //
        // Environment configuration //
        // ------------------------- //

        // Reset
        m_config_reset                = new;
        m_config_reset.active         = UVM_ACTIVE;
        m_config_reset.interface_name = "vif_reset";
        uvm_config_db #(uvm_reset::config_item)::set(this, "m_reset", "m_config", m_config_reset);
        m_reset = uvm_reset::agent::type_id::create("m_reset", this);

        // RX MVB
        for (int unsigned i = 0; i < RX_STREAMS; i++) begin
            m_config_rx_mvb[i]                = new;
            m_config_rx_mvb[i].active         = UVM_ACTIVE;
            m_config_rx_mvb[i].interface_name = $sformatf("vif_rx_mvb_%0d", i);
            uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, $sformatf("m_env_rx_mvb_%0d", i), "m_config", m_config_rx_mvb[i]);
            m_env_rx_mvb[i] = uvm_logic_vector_mvb::env_rx #(MVB_ITEMS, MVB_ITEM_WIDTH)::type_id::create($sformatf("m_env_rx_mvb_%0d", i), this);
        end

        // TX MVB
        m_config_tx_mvb                = new;
        m_config_tx_mvb.active         = UVM_ACTIVE;
        m_config_tx_mvb.interface_name = "vif_tx_mvb";
        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "m_env_tx_mvb", "m_config", m_config_tx_mvb);
        m_env_tx_mvb = uvm_logic_vector_mvb::env_tx #(MVB_ITEMS, MVB_ITEM_WIDTH)::type_id::create("m_env_tx_mvb", this);

        // ----------------------- //
        // Coverage model creation //
        // ----------------------- //

        m_hl_coverage_model = hl_coverage_model #(MVB_ITEM_WIDTH, RX_STREAMS)           ::type_id::create("m_hl_coverage_model", this);
        m_ll_coverage_model = ll_coverage_model #(MVB_ITEMS, MVB_ITEM_WIDTH, RX_STREAMS)::type_id::create("m_ll_coverage_model", this);
        for (int unsigned i = 0; i < RX_STREAMS; i++) begin
            m_coverage_rx_mvb[i] = new($sformatf("m_coverage_rx_mvb_%0d", i));
        end
        m_coverage_tx_mvb = new("m_coverage_tx_mvb");

        m_scoreboard        = scoreboard        #(MVB_ITEM_WIDTH, RX_STREAMS)           ::type_id::create("m_scoreboard", this);
        m_virtual_sequencer = virtual_sequencer #(MVB_ITEMS, MVB_ITEM_WIDTH, RX_STREAMS)::type_id::create("m_virtual_sequencer", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);

        // ---------------------- //
        // Environment connection //
        // ---------------------- //

        // Reset => RX MVB
        for (int unsigned i = 0; i < RX_STREAMS; i++) begin
            m_reset.sync_connect(m_env_rx_mvb[i].reset_sync);
        end
        // Reset -> TX MVB
        m_reset.sync_connect(m_env_tx_mvb.reset_sync);

        // RX MVB => Scoreboard
        for (int unsigned i = 0; i < RX_STREAMS; i++) begin
            m_env_rx_mvb[i].analysis_port.connect(m_scoreboard.analysis_export_rx_mvb[i]);
        end
        // TX MVB -> Scoreboard
        m_env_tx_mvb.analysis_port.connect(m_scoreboard.analysis_export_tx_mvb);

        // ------------------------- //
        // Coverage model connection //
        // ------------------------- //

        for (int unsigned i = 0; i < RX_STREAMS; i++) begin
            m_env_rx_mvb[i].analysis_port.connect(m_hl_coverage_model.analysis_export);
            m_env_rx_mvb[i].m_mvb_agent.analysis_port.connect(m_ll_coverage_model.in[i].analysis_export);
        end
        for (int unsigned i = 0; i < RX_STREAMS; i++) begin
            m_env_rx_mvb[i].m_mvb_agent.analysis_port.connect(m_coverage_rx_mvb[i].analysis_export);
        end
        m_env_tx_mvb.m_mvb_agent.analysis_port.connect(m_coverage_tx_mvb.analysis_export);

        // ---------------------------- //
        // Virtual sequencer connection //
        // ---------------------------- //

        m_virtual_sequencer.m_reset  = m_reset.m_sequencer;
        for (int unsigned i = 0; i < RX_STREAMS; i++) begin
            m_virtual_sequencer.m_rx_mvb[i] = m_env_rx_mvb[i].m_sequencer;
        end
        m_virtual_sequencer.m_tx_mvb = m_env_tx_mvb.m_sequencer;
    endfunction

endclass
