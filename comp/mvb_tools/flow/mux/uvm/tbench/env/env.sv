// env.sv: Verification environment
// Copyright (C) 2023 CESNET z. s. p. o.
// Author:   Oliver Gurka <xgurka00@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class lv_mvb#(
    int unsigned ITEMS,
    int unsigned ITEM_WIDTH
) extends uvm_logic_vector_mvb::env_rx #(ITEMS, ITEM_WIDTH);
    `uvm_component_param_utils(uvm_mvb_mux::lv_mvb #(ITEMS, ITEM_WIDTH));

     uvm_analysis_port #(uvm_mvb::sequence_item#(ITEMS, ITEM_WIDTH)) analysis_port_mvb;

    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void connect_phase(uvm_phase phase);
        analysis_port_mvb = m_mvb_agent.analysis_port;
        super.connect_phase(phase);
    endfunction

endclass

class env #(ITEMS, ITEM_WIDTH, RX_MVB_CNT) extends uvm_env;

    `uvm_component_param_utils(uvm_mvb_mux::env #(ITEMS, ITEM_WIDTH, RX_MVB_CNT));


    uvm_mvb_mux::virt_sequencer#(ITEM_WIDTH, RX_MVB_CNT) vscr;

    lv_mvb #(ITEMS, ITEM_WIDTH)           rx_env[RX_MVB_CNT];
    uvm_mvb::coverage #(ITEMS, ITEM_WIDTH)  tx_coverage;
    uvm_mvb::agent_tx #(ITEMS, ITEM_WIDTH)  tx_env;
    uvm_logic_vector_mvb::env_rx #(1, $clog2(RX_MVB_CNT))      rx_sel_env;

    uvm_reset::agent         m_reset;

    scoreboard #(ITEMS, ITEM_WIDTH, RX_MVB_CNT) m_scoreboard;

    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);
        uvm_mvb::config_item  cfg_tx;
        uvm_logic_vector_mvb::config_item  cfg_sel_rx;
        uvm_reset::config_item             m_config_reset;

        cfg_tx                = new;
        cfg_tx.active         = UVM_ACTIVE;
        cfg_tx.interface_name = "tx_vif";
        uvm_config_db #(uvm_mvb::config_item)::set(this, "tx_env", "m_config", cfg_tx);
        tx_env       = uvm_mvb::agent_tx #(ITEMS, ITEM_WIDTH)::type_id::create("tx_env", this);
        tx_coverage  = uvm_mvb::coverage #(ITEMS, ITEM_WIDTH)::type_id::create("tx_coverage", this);

        cfg_sel_rx            = new;
        cfg_sel_rx.active     = UVM_ACTIVE;
        cfg_sel_rx.interface_name = "sel_vif";
        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "rx_sel_env", "m_config", cfg_sel_rx);
        rx_sel_env = uvm_logic_vector_mvb::env_rx #(1, $clog2(RX_MVB_CNT))::type_id::create("rx_sel_env", this);

        for (int port = 0; port < RX_MVB_CNT; port++) begin
            uvm_logic_vector_mvb::config_item  cfg_rx;

            cfg_rx                = new;
            cfg_rx.active         = UVM_ACTIVE;
            cfg_rx.interface_name = $sformatf("rx_vif_%0d", port);
            cfg_rx.seq_cfg        = new();
            cfg_rx.seq_cfg.space_size_set(0, 5);
            cfg_rx.coverage       = 1;
            uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, $sformatf("rx_env_%0d", port), "m_config",
                                                                   cfg_rx);
            rx_env[port] = lv_mvb #(ITEMS, ITEM_WIDTH)::type_id::create($sformatf("rx_env_%0d", port), this);
        end

        m_config_reset                = new;
        m_config_reset.active         = UVM_ACTIVE;
        m_config_reset.interface_name = "vif_reset";
        uvm_config_db #(uvm_reset::config_item)::set(this, "m_reset", "m_config", m_config_reset);
        m_reset = uvm_reset::agent::type_id::create("m_reset", this);


        m_scoreboard = scoreboard #(ITEMS, ITEM_WIDTH, RX_MVB_CNT)::type_id::create("m_scoreboard", this);
        vscr         = uvm_mvb_mux::virt_sequencer#(ITEM_WIDTH, RX_MVB_CNT)::type_id::create("vscr",this);
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);

        tx_env.analysis_port.connect(m_scoreboard.analysis_imp_mvb_tx);
        tx_env.analysis_port.connect(tx_coverage.analysis_export);
        rx_sel_env.analysis_port.connect(m_scoreboard.analysis_imp_mvb_sel_rx);

        for (int port = 0; port < RX_MVB_CNT; port++) begin
            m_reset.sync_connect(rx_env[port].reset_sync);
            rx_env[port].analysis_port_mvb.connect(m_scoreboard.analysis_imp_mvb_rx[port]);
        end

        m_reset.sync_connect(tx_env.reset_sync);
        m_reset.sync_connect(rx_sel_env.reset_sync);

        vscr.m_reset = m_reset.m_sequencer;

        for (int port = 0; port < RX_MVB_CNT; port++) begin
            vscr.m_logic_vector_scr[port] = rx_env[port].m_sequencer;
        end
        vscr.m_logic_vector_sel_scr    = rx_sel_env.m_sequencer;

    endfunction
endclass
