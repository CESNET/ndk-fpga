// env.sv: Verification environment
// MVB_FORK UVM verification
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
//
// The environment contains one RX MVB environment (drives the fork input),
// OUTPUT_PORTS TX MVB environments (load the fork outputs with random
// back-pressure), one reset agent and the scoreboard.
//
// SPDX-License-Identifier: BSD-3-Clause

class env #(ITEMS, ITEM_WIDTH, OUTPUT_PORTS, USE_DST_RDY = 1) extends uvm_env;

    `uvm_component_param_utils(uvm_mvb_fork::env #(ITEMS, ITEM_WIDTH, OUTPUT_PORTS, USE_DST_RDY));

    uvm_logic_vector_mvb::env_rx #(ITEMS, ITEM_WIDTH) rx_env;
    uvm_logic_vector_mvb::config_item                 cfg_rx;

    uvm_logic_vector_mvb::env_tx #(ITEMS, ITEM_WIDTH) tx_env    [OUTPUT_PORTS];
    uvm_logic_vector_mvb::config_item                 cfg_tx    [OUTPUT_PORTS];

    uvm_reset::agent         m_reset;
    uvm_reset::config_item   m_config_reset;

    uvm_mvb_fork::virt_sequencer #(ITEM_WIDTH, OUTPUT_PORTS) vscr;
    scoreboard #(ITEM_WIDTH, OUTPUT_PORTS) m_scoreboard;

    // In directed mode the MVb agents are passive: the monitors keep running
    // no drivers/sequencers are created and no background random sequences are started
    bit agents_active;

    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
        agents_active = 1;
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);

        // Directed tests set "agents_active" to 0 before the environment is created
        uvm_config_db #(bit)::get(this, "", "agents_active", agents_active);

        m_config_reset                = new;
        m_config_reset.active         = UVM_ACTIVE;
        m_config_reset.interface_name = "vif_reset";

        uvm_config_db #(uvm_reset::config_item)::set(this, "m_reset", "m_config", m_config_reset);
        m_reset = uvm_reset::agent::type_id::create("m_reset", this);

        cfg_rx = new;
        cfg_rx.active = agents_active ? UVM_ACTIVE : UVM_PASSIVE;
        cfg_rx.coverage = 1;
        cfg_rx.interface_name = "vif_rx";
        cfg_rx.seq_cfg = new();
        cfg_rx.seq_cfg.space_size_set(0, 5);

        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "rx_env", "m_config", cfg_rx);
        rx_env = uvm_logic_vector_mvb::env_rx #(ITEMS, ITEM_WIDTH)::type_id::create("rx_env", this);

        for (int i = 0; i < OUTPUT_PORTS; i++) begin
            cfg_tx[i] = new;
            cfg_tx[i].active = agents_active ? UVM_ACTIVE : UVM_PASSIVE;
            cfg_tx[i].coverage = 1;
            cfg_tx[i].interface_name = $sformatf("vif_tx_%0d", i);
            cfg_tx[i].lib_type = USE_DST_RDY ? uvm_logic_vector_mvb::config_item::BASE
                                             : uvm_logic_vector_mvb::config_item::SPEED;

            uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, $sformatf("tx_env_%0d", i), "m_config",
                                                                     cfg_tx[i]);
            tx_env[i] = uvm_logic_vector_mvb::env_tx #(ITEMS, ITEM_WIDTH)::type_id::create(
                $sformatf("tx_env_%0d", i), this);
        end

        m_scoreboard = scoreboard #(ITEM_WIDTH, OUTPUT_PORTS)::type_id::create("m_scoreboard", this);
        vscr         = uvm_mvb_fork::virt_sequencer #(ITEM_WIDTH, OUTPUT_PORTS)::type_id::create("vscr", this);

    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);

        rx_env.analysis_port.connect(m_scoreboard.analysis_imp_mvb_rx);

        for (int i = 0; i < OUTPUT_PORTS; i++) begin
            tx_env[i].analysis_port.connect(m_scoreboard.analysis_imp_mvb_tx[i]);

            m_reset.sync_connect(rx_env.reset_sync);
            m_reset.sync_connect(tx_env[i].reset_sync);
        end

        vscr.m_reset            = m_reset.m_sequencer;
        vscr.m_logic_vector_scr = rx_env.m_sequencer;

    endfunction

endclass
