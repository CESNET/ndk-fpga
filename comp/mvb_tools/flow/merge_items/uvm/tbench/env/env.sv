// env.sv: Verification environment
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class env #(RX0_ITEMS, RX1_ITEMS, RX0_ITEM_WIDTH, RX1_ITEM_WIDTH, TX_ITEM_WIDTH) extends uvm_env;
    `uvm_component_param_utils(merge_items::env #(RX0_ITEMS, RX1_ITEMS, RX0_ITEM_WIDTH, RX1_ITEM_WIDTH, TX_ITEM_WIDTH));

    uvm_reset::agent m_reset;

    // RX environments
    uvm_logic_vector_mvb::env_rx #(RX0_ITEMS, RX0_ITEM_WIDTH) m_env_rx0;
    uvm_logic_vector_mvb::env_rx #(RX1_ITEMS, RX1_ITEM_WIDTH) m_env_rx1;

    // TX environments
    uvm_logic_vector_mvb::env_tx #(RX0_ITEMS, TX_ITEM_WIDTH)  m_env_tx;
    uvm_logic_vector_mvb::env_tx #(RX0_ITEMS, RX0_ITEM_WIDTH) m_env_tx0;
    uvm_logic_vector_mvb::env_tx #(RX0_ITEMS, RX1_ITEM_WIDTH) m_env_tx1;

    merge_items::virt_sequencer #(RX0_ITEMS, RX0_ITEM_WIDTH, RX1_ITEM_WIDTH, TX_ITEM_WIDTH) vscr;
    scoreboard                  #(RX0_ITEM_WIDTH, RX1_ITEM_WIDTH, TX_ITEM_WIDTH)            sc;

    uvm_mvb::coverage #(RX0_ITEMS, RX0_ITEM_WIDTH) m_cover_rx0;
    uvm_mvb::coverage #(RX1_ITEMS, RX1_ITEM_WIDTH) m_cover_rx1;
    uvm_mvb::coverage #(RX0_ITEMS, TX_ITEM_WIDTH)  m_cover_tx;
    uvm_mvb::coverage #(RX0_ITEMS, RX0_ITEM_WIDTH) m_cover_tx0;
    uvm_mvb::coverage #(RX0_ITEMS, RX1_ITEM_WIDTH) m_cover_tx1;

    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);

        uvm_reset::config_item            m_config_reset;
        uvm_logic_vector_mvb::config_item m_config_rx0;
        uvm_logic_vector_mvb::config_item m_config_rx1;
        uvm_logic_vector_mvb::config_item m_config_tx;
        uvm_logic_vector_mvb::config_item m_config_tx0;
        uvm_logic_vector_mvb::config_item m_config_tx1;

        m_config_reset                = new;
        m_config_reset.active         = UVM_ACTIVE;
        m_config_reset.interface_name = "vif_reset";
        uvm_config_db #(uvm_reset::config_item)::set(this, "m_reset", "m_config", m_config_reset);
        m_reset = uvm_reset::agent::type_id::create("m_reset", this);

        m_config_rx0                = new;
        m_config_rx0.active         = UVM_ACTIVE;
        m_config_rx0.interface_name = "vif_rx0";
        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "m_env_rx0", "m_config", m_config_rx0);
        m_env_rx0 = uvm_logic_vector_mvb::env_rx #(RX0_ITEMS, RX0_ITEM_WIDTH)::type_id::create("m_env_rx0", this);

        m_config_rx1                = new;
        m_config_rx1.active         = UVM_ACTIVE;
        m_config_rx1.interface_name = "vif_rx1";
        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "m_env_rx1", "m_config", m_config_rx1);
        m_env_rx1 = uvm_logic_vector_mvb::env_rx #(RX1_ITEMS, RX1_ITEM_WIDTH)::type_id::create("m_env_rx1", this);

        m_config_tx                = new;
        m_config_tx.active         = UVM_ACTIVE;
        m_config_tx.interface_name = "vif_tx";
        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "m_env_tx", "m_config", m_config_tx);
        m_env_tx = uvm_logic_vector_mvb::env_tx #(RX0_ITEMS, TX_ITEM_WIDTH)::type_id::create("m_env_tx", this);

        m_config_tx0                = new;
        m_config_tx0.active         = UVM_PASSIVE;
        m_config_tx0.interface_name = "vif_tx0";
        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "m_env_tx0", "m_config", m_config_tx0);
        m_env_tx0 = uvm_logic_vector_mvb::env_tx #(RX0_ITEMS, RX0_ITEM_WIDTH)::type_id::create("m_env_tx0", this);

        m_config_tx1                = new;
        m_config_tx1.active         = UVM_PASSIVE;
        m_config_tx1.interface_name = "vif_tx1";
        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "m_env_tx1", "m_config", m_config_tx1);
        m_env_tx1 = uvm_logic_vector_mvb::env_tx #(RX0_ITEMS, RX1_ITEM_WIDTH)::type_id::create("m_env_tx1", this);

        m_cover_rx0 = new("m_cover_rx0");
        m_cover_rx1 = new("m_cover_rx1");
        m_cover_tx  = new("m_cover_tx" );
        m_cover_tx0 = new("m_cover_tx0");
        m_cover_tx1 = new("m_cover_tx1");

        sc   = scoreboard                  #(RX0_ITEM_WIDTH, RX1_ITEM_WIDTH, TX_ITEM_WIDTH)           ::type_id::create("sc",   this);
        vscr = merge_items::virt_sequencer #(RX0_ITEMS, RX0_ITEM_WIDTH, RX1_ITEM_WIDTH, TX_ITEM_WIDTH)::type_id::create("vscr", this);

    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);

        m_env_rx0.analysis_port.connect(sc.analysis_imp_mvb_rx0);
        m_env_rx1.analysis_port.connect(sc.analysis_imp_mvb_rx1);

        m_env_tx .analysis_port.connect(sc.analysis_imp_mvb_tx );
        m_env_tx0.analysis_port.connect(sc.analysis_imp_mvb_tx0);
        m_env_tx1.analysis_port.connect(sc.analysis_imp_mvb_tx1);

        m_reset.sync_connect(m_env_rx0.reset_sync);
        m_reset.sync_connect(m_env_rx1.reset_sync);
        m_reset.sync_connect(m_env_tx.reset_sync );

        m_env_rx0.m_mvb_agent.analysis_port.connect(m_cover_rx0.analysis_export);
        m_env_rx1.m_mvb_agent.analysis_port.connect(m_cover_rx1.analysis_export);
        m_env_tx .m_mvb_agent.analysis_port.connect(m_cover_tx .analysis_export);
        m_env_tx0.m_mvb_agent.analysis_port.connect(m_cover_tx0.analysis_export);
        m_env_tx1.m_mvb_agent.analysis_port.connect(m_cover_tx1.analysis_export);

        vscr.m_reset         = m_reset.m_sequencer;
        vscr.m_mvb_data0_sqr = m_env_rx0.m_sequencer;
        vscr.m_mvb_data1_sqr = m_env_rx1.m_sequencer;
        vscr.m_mvb_rdy_sqr   = m_env_tx.m_sequencer;

    endfunction
endclass
