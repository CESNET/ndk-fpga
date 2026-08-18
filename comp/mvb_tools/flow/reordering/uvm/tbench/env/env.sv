// env.sv: Verification environment
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
// SPDX-License-Identifier: BSD-3-Clause

class env #(
    int unsigned ITEMS,
    int unsigned ITEM_WIDTH,
    bit REORDERING_EN
) extends uvm_env;
    `uvm_component_param_utils(uvm_mvb_reordering::env #(ITEMS, ITEM_WIDTH, REORDERING_EN))

    // Reset environment
    uvm_reset::agent m_reset;

    // RX environment
    // uvm_mvb::env_rx #(ITEMS, ITEM_WIDTH) m_env_rx_mvb;  + $clog2(ITEMS)
    uvm_mvb::agent_rx #(ITEMS, ITEM_WIDTH + $clog2(ITEMS)) m_agent_rx_mvb;

    // TX environment
    // uvm_mvb::env_tx #(ITEMS, ITEM_WIDTH) m_env_tx_mvb;
    uvm_mvb::agent_tx #(ITEMS, ITEM_WIDTH) m_agent_tx_mvb;

    // Coverage models
    coverage_model #(ITEMS, ITEM_WIDTH) m_coverage_model;

    // Scoreboard
    scoreboard #(ITEMS, ITEM_WIDTH, REORDERING_EN) m_scoreboard;
    // Virtual sequencer
    virtual_sequencer #(ITEMS, ITEM_WIDTH) m_virtual_sequencer;

    // Constructor
    function new(string name = "env", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        uvm_reset::config_item                  m_config_reset;
        uvm_mvb::config_item       m_config_rx_mvb;
        uvm_mvb::config_item       m_config_tx_mvb;

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
        //m_config_rx_mvb.coverage       = 1;
        uvm_config_db #(uvm_mvb::config_item)::set(this, "m_agent_rx_mvb", "m_config", m_config_rx_mvb);
        m_agent_rx_mvb = uvm_mvb::agent_rx #(
            ITEMS,
            ITEM_WIDTH + $clog2(ITEMS)
        )::type_id::create("m_agent_rx_mvb", this);

        // TX MVB
        m_config_tx_mvb                = new;
        m_config_tx_mvb.active         = UVM_ACTIVE;
        m_config_tx_mvb.interface_name = "vif_tx_mvb";
        //m_config_tx_mvb.coverage       = 1;
        uvm_config_db #(uvm_mvb::config_item)::set(this, "m_agent_tx_mvb", "m_config", m_config_tx_mvb);
        m_agent_tx_mvb = uvm_mvb::agent_tx #(
            ITEMS,
            ITEM_WIDTH
        )::type_id::create("m_agent_tx_mvb", this);

        // ----------------------- //
        // Coverage model creation //
        // ----------------------- //

        m_coverage_model    = coverage_model #(ITEMS, ITEM_WIDTH)::type_id::create("m_coverage_model", this);

        m_scoreboard        = scoreboard #(ITEMS, ITEM_WIDTH, REORDERING_EN)::type_id::create("m_scoreboard", this);

        m_virtual_sequencer = virtual_sequencer #(ITEMS, ITEM_WIDTH)::type_id::create("m_virtual_sequencer", this);


    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);

        // ---------------------- //
        // Environment connection //
        // ---------------------- //

        // Reset -> RX MVB
        m_reset.sync_connect(m_agent_rx_mvb.reset_sync);
        // Reset -> TX MVB
        m_reset.sync_connect(m_agent_tx_mvb.reset_sync);

        // RX MVB -> Scoreboard
        m_agent_rx_mvb.analysis_port.connect(m_scoreboard.analysis_export_rx_mvb);
        // TX MVB -> Scoreboard
        m_agent_tx_mvb.analysis_port.connect(m_scoreboard.analysis_export_tx_mvb);

        // ------------------------- //
        // Coverage model connection //scoreboard_dma_rc
        // ------------------------- //

        m_agent_rx_mvb.analysis_port.connect(m_coverage_model.analysis_export);

        // ---------------------------- //
        // Virtual sequencer connection //
        // ---------------------------- //

        m_virtual_sequencer.m_reset  = m_reset.m_sequencer;
        m_virtual_sequencer.m_rx_mvb = m_agent_rx_mvb.m_sequencer;
        m_virtual_sequencer.m_tx_mvb = m_agent_tx_mvb.m_sequencer;

        // // ------------------ //
        // // Mailbox connection //
        // // ------------------ //

        // uvm_config_db #(mailbox #(int unsigned))::set(this, "m_env_rx_mvb.m_logic_vector_agent.m_sequencer",
        //                                             "frame_lengths", m_virtual_sequencer.m_rx_mfb.frame_lengths);
    endfunction

endclass
