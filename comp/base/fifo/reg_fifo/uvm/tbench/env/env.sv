// env.sv: Verification environment
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class env #(DATA_WIDTH, ITEMS) extends uvm_env;
    `uvm_component_param_utils(uvm_fifo_registered::env #(DATA_WIDTH, ITEMS));

    uvm_reset::agent m_reset;

    uvm_logic_vector_mvb::env_rx #(1, DATA_WIDTH) m_env_mvb_rx;
    uvm_logic_vector_mvb::env_tx #(1, DATA_WIDTH) m_env_mvb_tx;

    // Coverages
    uvm_mvb::coverage #(1, DATA_WIDTH) m_cover_mvb_rx;
    uvm_mvb::coverage #(1, DATA_WIDTH) m_cover_mvb_tx;

    // Scoreboard
    scoreboard #(DATA_WIDTH, ITEMS) sc;
    // Virtual sequencer
    virt_sequencer #(DATA_WIDTH) vscr;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        // Creation of the coverages
        m_cover_mvb_rx     = new("m_cover_mvb_rx");
        m_cover_mvb_tx     = new("m_cover_mvb_tx");
    endfunction

    function void build_phase(uvm_phase phase);
        // Creation of the configuration items
        uvm_reset::config_item m_config_reset;
        uvm_logic_vector_mvb::config_item m_config_mvb_rx;
        uvm_logic_vector_mvb::config_item m_config_mvb_tx;

        // Configuration of the reset
        m_config_reset                = new;
        m_config_reset.active         = UVM_ACTIVE;
        m_config_reset.interface_name = "vif_reset";
        uvm_config_db #(uvm_reset::config_item)::set(this, "m_reset", "m_config", m_config_reset);
        // Creation of the reset
        m_reset = uvm_reset::agent::type_id::create("m_reset", this);

        // Configuration of the m_env_mvb_rx
        m_config_mvb_rx                = new;
        m_config_mvb_rx.active         = UVM_ACTIVE;
        m_config_mvb_rx.interface_name = "vif_mvb_rx";
        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "m_env_mvb_rx", "m_config", m_config_mvb_rx);
        // Creation of the m_env_mvb_rx
        m_env_mvb_rx = uvm_logic_vector_mvb::env_rx #(1, DATA_WIDTH)::type_id::create("m_env_mvb_rx", this);

        // Configuration of the m_env_mvb_tx
        m_config_mvb_tx                = new;
        m_config_mvb_tx.active         = UVM_ACTIVE;
        m_config_mvb_tx.interface_name = "vif_mvb_tx";
        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "m_env_mvb_tx", "m_config", m_config_mvb_tx);
        // Creation of the m_env_mvb_tx
        m_env_mvb_tx = uvm_logic_vector_mvb::env_tx #(1, DATA_WIDTH)::type_id::create("m_env_mvb_tx", this);

        // Creation of the scoreboard
        sc = scoreboard #(DATA_WIDTH, ITEMS)::type_id::create("sc", this);
        // Creation of the virtual sequencer
        vscr = virt_sequencer #(DATA_WIDTH)::type_id::create("vscr", this);
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);

        // Connection of the reset
        m_reset.sync_connect(m_env_mvb_rx    .reset_sync);
        m_reset.sync_connect(m_env_mvb_tx    .reset_sync);

        // RX environments connection
        m_env_mvb_rx.analysis_port.connect(sc.analysis_imp_mvb_rx);

        // TX environments connection
        m_env_mvb_tx.analysis_port.connect(sc.analysis_imp_mvb_tx);

        // Connections of the coverages
        m_env_mvb_rx    .m_mvb_agent.analysis_port.connect(m_cover_mvb_rx    .analysis_export);
        m_env_mvb_tx    .m_mvb_agent.analysis_port.connect(m_cover_mvb_tx    .analysis_export);

        // Passing the sequencers to the virtual sequencer
        vscr.m_reset = m_reset.m_sequencer;
        vscr.m_mvb_rx_sqr = m_env_mvb_rx.m_sequencer;
        vscr.m_mvb_tx_sqr = m_env_mvb_tx.m_sequencer;
    endfunction
endclass
