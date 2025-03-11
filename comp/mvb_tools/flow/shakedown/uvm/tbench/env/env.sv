// env.sv: Verification environment
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class env #(int unsigned RX_ITEMS, int unsigned TX_ITEMS, int unsigned ITEM_WIDTH) extends uvm_env;
    `uvm_component_param_utils(uvm_mvb_shakedown::env #(RX_ITEMS, TX_ITEMS, ITEM_WIDTH))

    // Reset environment
    uvm_reset::agent m_reset;

    // RX environment
    uvm_logic_vector_mvb::env_rx #(RX_ITEMS, ITEM_WIDTH) m_env_rx_mvb;

    // TX environments
    uvm_logic_vector_mvb::env_tx #(1, ITEM_WIDTH) m_env_tx_mvb[TX_ITEMS];

    // Coverage models
    ll_coverage_model #(TX_ITEMS, ITEM_WIDTH) m_coverage_model;
    uvm_mvb::coverage #(RX_ITEMS, ITEM_WIDTH) m_coverage_rx_mvb;
    uvm_mvb::coverage #(1, ITEM_WIDTH)        m_coverage_tx_mvb[TX_ITEMS];

    // Scoreboard
    scoreboard #(RX_ITEMS, TX_ITEMS, ITEM_WIDTH) m_scoreboard;
    // Virtual sequencer
    virtual_sequencer #(TX_ITEMS, ITEM_WIDTH) m_virtual_sequencer;

    // Port activity detector
    activity_detector #(TX_ITEMS, ITEM_WIDTH) m_activity_detector;

    // Constructor
    function new(string name = "env", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        uvm_reset::config_item            m_config_reset;
        uvm_logic_vector_mvb::config_item m_config_rx_mvb;
        uvm_logic_vector_mvb::config_item m_config_tx_mvb[TX_ITEMS];

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
        m_config_rx_mvb                = new;
        m_config_rx_mvb.active         = UVM_ACTIVE;
        m_config_rx_mvb.interface_name = "vif_rx_mvb";
        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "m_env_rx_mvb", "m_config", m_config_rx_mvb);
        m_env_rx_mvb = uvm_logic_vector_mvb::env_rx #(RX_ITEMS, ITEM_WIDTH)::type_id::create("m_env_rx_mvb", this);

        // TX MVB
        for (int unsigned i = 0; i < TX_ITEMS; i++) begin
            m_config_tx_mvb[i]                = new;
            m_config_tx_mvb[i].active         = UVM_ACTIVE;
            m_config_tx_mvb[i].interface_name = $sformatf("vif_tx_mvb_%0d", i);
            uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, $sformatf("m_env_tx_mvb_%0d", i), "m_config", m_config_tx_mvb[i]);
            m_env_tx_mvb[i] = uvm_logic_vector_mvb::env_tx #(1, ITEM_WIDTH)::type_id::create($sformatf("m_env_tx_mvb_%0d", i), this);
        end

        // ----------------------- //
        // Coverage model creation //
        // ----------------------- //

        m_coverage_model = ll_coverage_model #(TX_ITEMS, ITEM_WIDTH)::type_id::create("m_coverage_model", this);
        m_coverage_rx_mvb = new("m_coverage_rx_mvb");
        for (int unsigned i = 0; i < TX_ITEMS; i++) begin
            m_coverage_tx_mvb[i] = new($sformatf("m_coverage_tx_mvb_%0d", i));
        end

        m_scoreboard        = scoreboard        #(RX_ITEMS, TX_ITEMS, ITEM_WIDTH)::type_id::create("m_scoreboard", this);
        m_virtual_sequencer = virtual_sequencer #(TX_ITEMS, ITEM_WIDTH)          ::type_id::create("m_virtual_sequencer", this);

        m_activity_detector = activity_detector #(TX_ITEMS, ITEM_WIDTH)::type_id::create("m_activity_detector", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);

        // ---------------------- //
        // Environment connection //
        // ---------------------- //

        // Reset -> RX MVB
        m_reset.sync_connect(m_env_rx_mvb.reset_sync);
        // Reset => TX MVB
        for (int unsigned i = 0; i < TX_ITEMS; i++) begin
            m_reset.sync_connect(m_env_tx_mvb[i].reset_sync);
        end

        // RX MVB -> Scoreboard
        m_env_rx_mvb.analysis_port.connect(m_scoreboard.analysis_export_rx_mvb);
        // TX MVB => Scoreboard
        for (int unsigned i = 0; i < TX_ITEMS; i++) begin
            m_env_tx_mvb[i].analysis_port.connect(m_scoreboard.analysis_export_tx_mvb[i]);
        end

        // ------------------------- //
        // Coverage model connection //
        // ------------------------- //

        for (int unsigned i = 0; i < TX_ITEMS; i++) begin
            m_env_tx_mvb[i].m_mvb_agent.analysis_port.connect(m_coverage_model.in[i].analysis_export);
        end

        m_env_rx_mvb.m_mvb_agent.analysis_port.connect(m_coverage_rx_mvb.analysis_export);
        for (int unsigned i = 0; i < TX_ITEMS; i++) begin
            m_env_tx_mvb[i].m_mvb_agent.analysis_port.connect(m_coverage_tx_mvb[i].analysis_export);
        end

        // ---------------------------- //
        // Virtual sequencer connection //
        // ---------------------------- //

        m_virtual_sequencer.m_reset  = m_reset.m_sequencer;
        m_virtual_sequencer.m_rx_mvb = m_env_rx_mvb.m_sequencer;
        for (int unsigned i = 0; i < TX_ITEMS; i++) begin
            m_virtual_sequencer.m_tx_mvb[i] = m_env_tx_mvb[i].m_sequencer;
        end

        // ---------------------------- //
        // Activity Detector connection //
        // ---------------------------- //

        for (int unsigned i = 0; i < TX_ITEMS; i++) begin
            m_env_tx_mvb[i].m_mvb_agent.analysis_port.connect(m_activity_detector.in[i].analysis_export);
        end
        m_activity_detector.analysis_port.connect(m_scoreboard.analysis_export_tx_read_command);
    endfunction

endclass
