// env.sv: Verification environment
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kriz <danielkriz@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

// Environment for the functional verification.
class env #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, META_WIDTH, MVB_DATA_WIDTH, MVB_ITEMS, PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH) extends uvm_env;
    `uvm_component_param_utils(uvm_items_valid::env #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, META_WIDTH, MVB_DATA_WIDTH, MVB_ITEMS, PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH));

    uvm_logic_vector_array_mfb::env_rx #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, META_WIDTH) m_env_rx;
    uvm_logic_vector_mvb::env_tx       #(MVB_ITEMS, MVB_DATA_WIDTH)                                                m_env_tx_mvb;
    uvm_logic_vector_mvb::env_tx       #(MVB_ITEMS, 1)                                                     m_env_end_mvb;

    uvm_items_valid::virt_sequencer #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, META_WIDTH, MVB_DATA_WIDTH, PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH) vscr;

    driver#(MFB_ITEM_WIDTH, META_WIDTH, PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH) m_driver;

    uvm_reset::agent                                             m_reset;
    uvm_header_type::agent#(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH) m_info_agent;

    scoreboard #(META_WIDTH, MVB_DATA_WIDTH, MVB_ITEMS, MFB_ITEM_WIDTH, OFFSET_WIDTH, LENGTH_WIDTH) sc;

    // Constructor of the environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Create base components of the environment.
    function void build_phase(uvm_phase phase);

        uvm_reset::config_item                  m_config_reset;
        uvm_logic_vector_array_mfb::config_item m_config_rx;
        uvm_header_type::config_item            m_info_agent_cfg;
        uvm_logic_vector_mvb::config_item       m_config_mvb_tx;
        uvm_logic_vector_mvb::config_item       m_config_mvb_end;

        m_info_agent_cfg        = new();
        m_info_agent_cfg.active = UVM_ACTIVE;
        uvm_config_db #(uvm_header_type::config_item)::set(this, "m_info_agent", "m_config", m_info_agent_cfg);
        m_info_agent = uvm_header_type::agent#(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH)::type_id::create("m_info_agent", this);

        m_config_reset                = new;
        m_config_reset.active         = UVM_ACTIVE;
        m_config_reset.interface_name = "vif_reset";

        uvm_config_db #(uvm_reset::config_item)::set(this, "m_reset", "m_config", m_config_reset);
        m_reset = uvm_reset::agent::type_id::create("m_reset", this);

        // Passing the virtual interfaces
        m_config_rx                = new;
        m_config_rx.active         = UVM_ACTIVE;
        m_config_rx.interface_name = "vif_rx";
        m_config_rx.meta_behav     = uvm_logic_vector_array_mfb::config_item::META_SOF;

        uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, "m_env_rx", "m_config", m_config_rx);
        m_env_rx = uvm_logic_vector_array_mfb::env_rx#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, META_WIDTH)::type_id::create("m_env_rx", this);

        m_config_mvb_tx                = new;
        m_config_mvb_tx.active         = UVM_ACTIVE;
        m_config_mvb_tx.interface_name = "vif_mvb_tx";

        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "m_env_tx_mvb", "m_config", m_config_mvb_tx);
        m_env_tx_mvb = uvm_logic_vector_mvb::env_tx#(MVB_ITEMS, MVB_DATA_WIDTH)::type_id::create("m_env_tx_mvb", this);

        m_config_mvb_end                = new;
        m_config_mvb_end.active         = UVM_PASSIVE;
        m_config_mvb_end.interface_name = "vif_mvb_end";

        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "m_env_end_mvb", "m_config", m_config_mvb_end);
        m_env_end_mvb = uvm_logic_vector_mvb::env_tx#(MVB_ITEMS, 1)::type_id::create("m_env_end_mvb", this);

        sc       = scoreboard#(META_WIDTH, MVB_DATA_WIDTH, MVB_ITEMS, MFB_ITEM_WIDTH, OFFSET_WIDTH, LENGTH_WIDTH)::type_id::create("sc", this);
        m_driver = driver #(MFB_ITEM_WIDTH, META_WIDTH, PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH)::type_id::create("m_driver", this);
        vscr     = uvm_items_valid::virt_sequencer#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, META_WIDTH, MVB_DATA_WIDTH, PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH)::type_id::create("vscr",this);

    endfunction

    // Connect agent's ports with ports from the scoreboard.
    function void connect_phase(uvm_phase phase);

        m_env_rx.analysis_port_data.connect(sc.input_mfb);
        m_env_rx.analysis_port_meta.connect(sc.input_meta);
        m_env_tx_mvb.analysis_port.connect(sc.out_mvb);
        m_env_end_mvb.analysis_port.connect(sc.end_mvb);

        m_reset.sync_connect(m_env_rx.reset_sync);
        m_reset.sync_connect(m_env_tx_mvb.reset_sync);
        m_reset.sync_connect(m_env_end_mvb.reset_sync);

        vscr.m_info           = m_info_agent.m_sequencer;

        m_driver.seq_item_port_info.connect(m_info_agent.m_sequencer.seq_item_export);

    endfunction

    virtual task run_phase(uvm_phase phase);
        logic_vector_sequence #(META_WIDTH) logic_vector_seq;
        byte_array_sequence#(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH, MFB_ITEM_WIDTH) byte_array_seq;

        logic_vector_seq           = logic_vector_sequence #(META_WIDTH)::type_id::create("logic_vector_seq", this);
        logic_vector_seq.tr_export = m_driver.logic_vector_export;
        logic_vector_seq.randomize();
        byte_array_seq           = byte_array_sequence#(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH, MFB_ITEM_WIDTH)::type_id::create("byte_array_seq", this);
        byte_array_seq.tr_export = m_driver.frame_export;
        byte_array_seq.randomize();

        fork
            logic_vector_seq.start(m_env_rx.m_sequencer.m_meta);
            byte_array_seq.start(m_env_rx.m_sequencer.m_data);
        join_none
    endtask

endclass
