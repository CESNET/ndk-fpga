// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Tomáš Neckař <xneckat00@stud.fit.vut.cz>
// SPDX-License-Identifier: BSD-3-Clause

class env #(
    int unsigned RX_ITEMS,
    int unsigned RX_ITEM_WIDTH,
    int unsigned TX_ITEMS,
    int unsigned TX_ITEM_WIDTH,
    int unsigned TUSER_WIDTH
) extends uvm_env;
    `uvm_component_param_utils(uvm_vector2packet::env #(RX_ITEMS, RX_ITEM_WIDTH, TX_ITEMS, TX_ITEM_WIDTH, TUSER_WIDTH));

    // Virtual sequencer
    sequencer #(RX_ITEMS, RX_ITEM_WIDTH, TX_ITEMS, TX_ITEM_WIDTH, TUSER_WIDTH) m_sequencer;

    // RESET interface
    protected uvm_reset::agent m_reset;
    // RX environments
    protected uvm_axi::agent_rx #(RX_ITEMS, RX_ITEM_WIDTH, TUSER_WIDTH) m_rx;
    // TX environments
    protected uvm_axi::agent_tx #(TX_ITEMS, TX_ITEM_WIDTH, TUSER_WIDTH) m_tx;

    // Scoreboard
    protected scoreboard #(TX_ITEMS, TX_ITEM_WIDTH, TUSER_WIDTH) m_sc;
    // Model instance
    protected uvm_vector2packet::model #(RX_ITEMS, RX_ITEM_WIDTH, TX_ITEMS, TX_ITEM_WIDTH, TUSER_WIDTH) m_model;

    // Constructor
    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= (m_model.used() != 0);
        ret |= (m_sc.used() != 0);
        return ret;
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);
        uvm_reset::config_item m_cfg_reset;
        uvm_axi::config_item m_cfg_rx;
        uvm_axi::config_item m_cfg_tx;

        //Call parents function build_phase
        super.build_phase(phase);

        //Create reset environment
        m_cfg_reset                = new;
        m_cfg_reset.active         = UVM_ACTIVE;   // Activly driven environment
        // interface register name have to be same in testbench uvm_config_db#(...)::set();
        m_cfg_reset.interface_name = "vif_reset";
        uvm_config_db #(uvm_reset::config_item)::set(this, "m_reset", "m_config", m_cfg_reset);
        // Creation of the reset
        m_reset = uvm_reset::agent::type_id::create("m_reset", this);


        // Configuration of the m_rx
        m_cfg_rx                = new;
        m_cfg_rx.active         = UVM_ACTIVE;
        // interface register name has to be same in testbench uvm_config_db#(...)::set();
        m_cfg_rx.interface_name = "vif_axi_rx";
        uvm_config_db #(uvm_axi::config_item)::set(this, "m_rx", "m_config", m_cfg_rx);
        // Creation of the m_rx
        m_rx = uvm_axi::agent_rx #(RX_ITEMS, RX_ITEM_WIDTH, TUSER_WIDTH)::type_id::create("m_rx", this);

        // Configuration of the m_tx
        m_cfg_tx                = new;
        m_cfg_tx.active         = UVM_ACTIVE;
        // interface register name has to be same in testbench uvm_config_db#(...)::set();
        m_cfg_tx.interface_name = "vif_axi_tx";
        uvm_config_db #(uvm_axi::config_item)::set(this, "m_tx", "m_config", m_cfg_tx);
        // Creation of the m_tx
        m_tx = uvm_axi::agent_tx #(TX_ITEMS, TX_ITEM_WIDTH, TUSER_WIDTH)::type_id::create("m_tx", this);

        // Create sequencer
        m_sequencer = sequencer #(
            RX_ITEMS, RX_ITEM_WIDTH, TX_ITEMS, TX_ITEM_WIDTH, TUSER_WIDTH
        )::type_id::create("m_sequencer", this);

        m_sc = scoreboard #(TX_ITEMS, TX_ITEM_WIDTH, TUSER_WIDTH)::type_id::create("m_sc", this);

        m_model = uvm_vector2packet::model #(
            RX_ITEMS, RX_ITEM_WIDTH, TX_ITEMS, TX_ITEM_WIDTH, TUSER_WIDTH
        )::type_id::create("m_model", this);
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);
        // Connection of the reset
        //m_reset.sync_connect(m_rx.reset_sync);
        //m_reset.sync_connect(m_tx.reset_sync);

        // Connection to scoreboard
        m_rx.analysis_port.connect(m_model.m_rx.analysis_export);
        // Connect to Scoreboard
        m_model.m_tx.connect(m_sc.cmp.analysis_imp_model);
        m_tx.analysis_port.connect(m_sc.cmp.analysis_imp_dut);

        // Connect sequencer
        m_sequencer.m_reset = m_reset.m_sequencer;
        m_sequencer.m_rx    = m_rx.m_sequencer;
        m_sequencer.m_tx    = m_tx.m_sequencer;
    endfunction
endclass
