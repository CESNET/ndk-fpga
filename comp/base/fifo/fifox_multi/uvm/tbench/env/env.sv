// env.sv: Verification environment
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class env #(DATA_WIDTH, ITEMS, WRITE_PORTS, READ_PORTS, ALMOST_FULL_OFFSET, ALMOST_EMPTY_OFFSET, IMPL_SHAKEDOWN) extends uvm_env;
    `uvm_component_param_utils(uvm_fifox_multi::env #(DATA_WIDTH, ITEMS, WRITE_PORTS, READ_PORTS, ALMOST_FULL_OFFSET, ALMOST_EMPTY_OFFSET, IMPL_SHAKEDOWN));

    uvm_reset::agent m_reset;

    // RX environments
    uvm_logic_vector_mvb::env_rx #(WRITE_PORTS, DATA_WIDTH) m_env_mvb_rx;
    uvm_logic_vector_mvb::env_rx #(READ_PORTS, 1)           m_env_mvb_rd;

    // TX environments
    uvm_logic_vector_mvb::env_tx #(READ_PORTS, DATA_WIDTH) m_env_mvb_tx;
    uvm_logic_vector_mvb::env_tx #(1, 2)                   m_env_mvb_status;

    // Coverages
    uvm_mvb::coverage #(WRITE_PORTS, DATA_WIDTH) m_cover_mvb_rx;
    uvm_mvb::coverage #(READ_PORTS, DATA_WIDTH)  m_cover_mvb_tx;
    uvm_mvb::coverage #(READ_PORTS, 1)           m_cover_mvb_rd;
    uvm_mvb::coverage #(1, 2)                    m_cover_mvb_status;

    // Scoreboard
    scoreboard #(DATA_WIDTH, ITEMS, WRITE_PORTS, READ_PORTS, ALMOST_FULL_OFFSET, ALMOST_EMPTY_OFFSET, IMPL_SHAKEDOWN) sc;
    // Virtual sequencer
    virt_sequencer #(DATA_WIDTH) vscr;

    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);

        // Creation of the coverages
        m_cover_mvb_rx     = new("m_cover_mvb_rx"    );
        m_cover_mvb_rd     = new("m_cover_mvb_rd"    );
        m_cover_mvb_tx     = new("m_cover_mvb_tx"    );
        m_cover_mvb_status = new("m_cover_mvb_status");

    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);

        // Creation of the configuration items
        uvm_reset::config_item m_config_reset;
        uvm_logic_vector_mvb::config_item m_config_mvb_rx;
        uvm_logic_vector_mvb::config_item m_config_mvb_rd;
        uvm_logic_vector_mvb::config_item m_config_mvb_tx;
        uvm_logic_vector_mvb::config_item m_config_mvb_status;

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
        m_env_mvb_rx = uvm_logic_vector_mvb::env_rx #(WRITE_PORTS, DATA_WIDTH)::type_id::create("m_env_mvb_rx", this);

        // Configuration of the m_env_mvb_rd
        m_config_mvb_rd                = new;
        m_config_mvb_rd.active         = UVM_ACTIVE;
        m_config_mvb_rd.interface_name = "vif_mvb_rd";
        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "m_env_mvb_rd", "m_config", m_config_mvb_rd);
        // Creation of the m_env_mvb_rd
        m_env_mvb_rd = uvm_logic_vector_mvb::env_rx #(READ_PORTS, 1)::type_id::create("m_env_mvb_rd", this);

        // Configuration of the m_env_mvb_tx
        m_config_mvb_tx                = new;
        m_config_mvb_tx.active         = UVM_PASSIVE;
        m_config_mvb_tx.interface_name = "vif_mvb_tx";
        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "m_env_mvb_tx", "m_config", m_config_mvb_tx);
        // Creation of the m_env_mvb_tx
        m_env_mvb_tx = uvm_logic_vector_mvb::env_tx #(READ_PORTS, DATA_WIDTH)::type_id::create("m_env_mvb_tx", this);

        // Configuration of the m_env_mvb_status
        m_config_mvb_status                = new;
        m_config_mvb_status.active         = UVM_PASSIVE;
        m_config_mvb_status.interface_name = "vif_mvb_status";
        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "m_env_mvb_status", "m_config", m_config_mvb_status);
        // Creation of the m_env_mvb_status
        m_env_mvb_status = uvm_logic_vector_mvb::env_tx #(1, 2)::type_id::create("m_env_mvb_status", this);

        // Creation of the scoreboard
        sc = scoreboard #(DATA_WIDTH, ITEMS, WRITE_PORTS, READ_PORTS, ALMOST_FULL_OFFSET, ALMOST_EMPTY_OFFSET, IMPL_SHAKEDOWN)::type_id::create("sc", this);
        // Creation of the virtual sequencer
        vscr = virt_sequencer #(DATA_WIDTH)::type_id::create("vscr", this);

    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);

        // Connection of the reset
        m_reset.sync_connect(m_env_mvb_rx    .reset_sync);
        m_reset.sync_connect(m_env_mvb_rd    .reset_sync);
        m_reset.sync_connect(m_env_mvb_tx    .reset_sync);
        m_reset.sync_connect(m_env_mvb_status.reset_sync);

        // RX environments connection
        m_env_mvb_rx.analysis_port.connect(sc.analysis_imp_mvb_rx);

        // TX environments connection
        m_env_mvb_tx.analysis_port.connect(sc.analysis_imp_mvb_tx);
        if (!IMPL_SHAKEDOWN) m_env_mvb_status.analysis_port.connect(sc.analysis_imp_mvb_status);

        // Connections of the coverages
        m_env_mvb_rx    .m_mvb_agent.analysis_port.connect(m_cover_mvb_rx    .analysis_export);
        m_env_mvb_rd    .m_mvb_agent.analysis_port.connect(m_cover_mvb_rd    .analysis_export);
        m_env_mvb_tx    .m_mvb_agent.analysis_port.connect(m_cover_mvb_tx    .analysis_export);
        m_env_mvb_status.m_mvb_agent.analysis_port.connect(m_cover_mvb_status.analysis_export);

        // Passing the sequencers to the virtual sequencer
        vscr.m_reset = m_reset.m_sequencer;
        vscr.m_mvb_rx_sqr = m_env_mvb_rx.m_sequencer;
        vscr.m_mvb_rd_sqr = m_env_mvb_rd.m_sequencer;

    endfunction

endclass
