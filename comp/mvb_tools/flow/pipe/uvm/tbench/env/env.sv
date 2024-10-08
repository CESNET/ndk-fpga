//-- env.sv: Verification environment
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// Environment for functional verification of encode.
// This environment containts two mii agents.
class env #(ITEMS, ITEM_WIDTH) extends uvm_env;

    `uvm_component_param_utils(uvm_pipe::env #(ITEMS, ITEM_WIDTH));

    uvm_logic_vector_mvb::env_rx #(ITEMS, ITEM_WIDTH) rx_env;
    uvm_logic_vector_mvb::config_item                 cfg_rx;
    uvm_logic_vector_mvb::env_tx #(ITEMS, ITEM_WIDTH) tx_env;
    uvm_logic_vector_mvb::config_item                 cfg_tx;

    uvm_pipe::virt_sequencer#(ITEM_WIDTH) vscr;
    uvm_reset::agent         m_reset;
    uvm_reset::config_item   m_config_reset;

    scoreboard #(ITEM_WIDTH) m_scoreboard;

    uvm_mvb::coverage #(ITEMS, ITEM_WIDTH) m_cover_rx;
    uvm_mvb::coverage #(ITEMS, ITEM_WIDTH) m_cover_tx;

    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);

        m_cover_rx = new("m_cover_rx");
        m_cover_tx = new("m_cover_tx");
        cfg_tx = new;
        cfg_rx = new;

        cfg_tx.active = UVM_ACTIVE;
        cfg_rx.active = UVM_ACTIVE;

        cfg_tx.interface_name = "vif_tx";
        cfg_rx.interface_name = "vif_rx";

        cfg_rx.seq_cfg = new();
        cfg_rx.seq_cfg.space_size_set(0, 5);

        m_config_reset                = new;
        m_config_reset.active         = UVM_ACTIVE;
        m_config_reset.interface_name = "vif_reset";

        uvm_config_db #(uvm_reset::config_item)::set(this, "m_reset", "m_config", m_config_reset);
        m_reset = uvm_reset::agent::type_id::create("m_reset", this);

        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "tx_env", "m_config", cfg_tx);
        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "rx_env", "m_config", cfg_rx);

        tx_env    = uvm_logic_vector_mvb::env_tx #(ITEMS, ITEM_WIDTH)::type_id::create("tx_env", this);
        rx_env    = uvm_logic_vector_mvb::env_rx #(ITEMS, ITEM_WIDTH)::type_id::create("rx_env", this);

        m_scoreboard  = scoreboard #(ITEM_WIDTH)::type_id::create("m_scoreboard", this);
        vscr   = uvm_pipe::virt_sequencer#(ITEM_WIDTH)::type_id::create("vscr",this);
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);

        rx_env.analysis_port.connect(m_scoreboard.analysis_imp_mvb_rx);
        tx_env.analysis_port.connect(m_scoreboard.analysis_imp_mvb_tx);

        m_reset.sync_connect(rx_env.reset_sync);
        m_reset.sync_connect(tx_env.reset_sync);

        rx_env.m_mvb_agent.analysis_port.connect(m_cover_rx.analysis_export);
        tx_env.m_mvb_agent.analysis_port.connect(m_cover_tx.analysis_export);

        vscr.m_reset            = m_reset.m_sequencer;
        vscr.m_logic_vector_scr = rx_env.m_sequencer;

    endfunction
endclass
