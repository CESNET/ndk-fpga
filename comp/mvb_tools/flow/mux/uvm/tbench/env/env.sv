// env.sv: Verification environment
// Copyright (C) 2023 CESNET z. s. p. o.
// Author:   Oliver Gurka <xgurka00@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class env #(ITEMS, ITEM_WIDTH, RX_MVB_CNT) extends uvm_env;

    `uvm_component_param_utils(uvm_mvb_mux::env #(ITEMS, ITEM_WIDTH, RX_MVB_CNT));

    uvm_logic_vector_mvb::env_rx #(ITEMS, ITEM_WIDTH) rx_env[RX_MVB_CNT - 1 : 0];
    uvm_logic_vector_mvb::config_item                 cfg_rx[RX_MVB_CNT - 1 : 0];
    uvm_logic_vector_mvb::env_tx #(ITEMS, ITEM_WIDTH) tx_env;
    uvm_logic_vector_mvb::config_item                 cfg_tx;
    uvm_logic_vector_mvb::env_rx #(1, $clog2(RX_MVB_CNT))      rx_sel_env;
    uvm_logic_vector_mvb::config_item                 cfg_sel_rx;

    uvm_mvb_mux::virt_sequencer#(ITEM_WIDTH, RX_MVB_CNT) vscr;
    uvm_reset::agent         m_reset;
    uvm_reset::config_item   m_config_reset;

    scoreboard #(ITEMS, ITEM_WIDTH, RX_MVB_CNT) m_scoreboard;

    uvm_mvb::coverage #(ITEMS, ITEM_WIDTH) m_cover_rx;
    uvm_mvb::coverage #(ITEMS, ITEM_WIDTH) m_cover_tx;

    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);

        m_cover_rx            = new("m_cover_rx");
        m_cover_tx            = new("m_cover_tx");

        cfg_tx                = new;
        cfg_tx.active         = UVM_ACTIVE;
        cfg_tx.interface_name = "tx_vif";

        cfg_sel_rx            = new;
        cfg_sel_rx.active     = UVM_ACTIVE;
        cfg_sel_rx.interface_name = "sel_vif";

        for (int port = 0; port < RX_MVB_CNT; port++) begin
            cfg_rx[port]                = new;
            cfg_rx[port].active         = UVM_ACTIVE;
            cfg_rx[port].interface_name = $sformatf("rx_vif_%0d", port);
            uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, $sformatf("rx_env_%0d", port), "m_config", cfg_rx[port]);
            rx_env[port] = uvm_logic_vector_mvb::env_rx #(ITEMS, ITEM_WIDTH)::type_id::create($sformatf("rx_env_%0d", port), this);
            cfg_rx[port].seq_cfg        = new();
            cfg_rx[port].seq_cfg.space_size_set(0, 5);
        end

        m_config_reset                = new;
        m_config_reset.active         = UVM_ACTIVE;
        m_config_reset.interface_name = "vif_reset";

        uvm_config_db #(uvm_reset::config_item)::set(this, "m_reset", "m_config", m_config_reset);
        m_reset = uvm_reset::agent::type_id::create("m_reset", this);

        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "tx_env", "m_config", cfg_tx);
        tx_env       = uvm_logic_vector_mvb::env_tx #(ITEMS, ITEM_WIDTH)::type_id::create("tx_env", this);

        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "rx_sel_env", "m_config", cfg_sel_rx);
        rx_sel_env = uvm_logic_vector_mvb::env_rx #(1, $clog2(RX_MVB_CNT))::type_id::create("rx_sel_env", this);

        m_scoreboard = scoreboard #(ITEMS, ITEM_WIDTH, RX_MVB_CNT)::type_id::create("m_scoreboard", this);
        vscr         = uvm_mvb_mux::virt_sequencer#(ITEM_WIDTH, RX_MVB_CNT)::type_id::create("vscr",this);
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);

        tx_env.m_mvb_agent.analysis_port.connect(m_scoreboard.analysis_imp_mvb_tx);
        rx_sel_env.analysis_port.connect(m_scoreboard.analysis_imp_mvb_sel_rx);

        for (int port = 0; port < RX_MVB_CNT; port++) begin
            m_reset.sync_connect(rx_env[port].reset_sync);
            rx_env[port].m_mvb_agent.analysis_port.connect(m_cover_rx.analysis_export);
            rx_env[port].m_mvb_agent.analysis_port.connect(m_scoreboard.analysis_imp_mvb_rx[port]);
        end

        m_reset.sync_connect(tx_env.reset_sync);
        m_reset.sync_connect(rx_sel_env.reset_sync);

        tx_env.m_mvb_agent.analysis_port.connect(m_cover_tx.analysis_export);

        vscr.m_reset = m_reset.m_sequencer;

        for (int port = 0; port < RX_MVB_CNT; port++)
            vscr.m_logic_vector_scr[port] = rx_env[port].m_sequencer;

        vscr.m_logic_vector_sel_scr    = rx_sel_env.m_sequencer;

    endfunction
endclass
