// env.sv: Verification environment
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class env #(int unsigned MFB_REGIONS, int unsigned MFB_REGION_SIZE, int unsigned MFB_BLOCK_SIZE, int unsigned MFB_ITEM_WIDTH, int unsigned PKT_MTU, int unsigned USERMETA_WIDTH, int unsigned RX_MVB_ITEM_WIDTH) extends uvm_env;
    `uvm_component_param_utils(uvm_mfb_frame_extender::env #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, PKT_MTU, USERMETA_WIDTH, RX_MVB_ITEM_WIDTH))

    // Reset environment
    uvm_reset::agent m_reset;

    // RX environments
    uvm_logic_vector_array_mfb::env_rx #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0) m_env_rx_mfb;
    uvm_logic_vector_mvb::env_rx       #(MFB_REGIONS, RX_MVB_ITEM_WIDTH)                                  m_env_rx_mvb;

    // TX environments
    uvm_logic_vector_array_mfb::env_tx #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, USERMETA_WIDTH) m_env_tx_mfb;
    uvm_logic_vector_mvb::env_tx       #(MFB_REGIONS, USERMETA_WIDTH)                                                  m_env_tx_mvb;

    // Scoreboard
    scoreboard #(MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, PKT_MTU, USERMETA_WIDTH, RX_MVB_ITEM_WIDTH) m_scoreboard;
    // Virtual sequencer
    virtual_sequencer #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, USERMETA_WIDTH, RX_MVB_ITEM_WIDTH) m_virtual_sequencer;

    // Constructor
    function new(string name = "env", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        uvm_reset::config_item                  m_config_reset;
        uvm_logic_vector_array_mfb::config_item m_config_rx_mfb;
        uvm_logic_vector_mvb::config_item       m_config_rx_mvb;
        uvm_logic_vector_array_mfb::config_item m_config_tx_mfb;
        uvm_logic_vector_mvb::config_item       m_config_tx_mvb;

        super.build_phase(phase);

        // ------------------- //
        // Database overriding //
        // ------------------- //

        uvm_logic_vector_array::sequencer #(MFB_ITEM_WIDTH)::type_id::set_inst_override(
            sequencer_length_extractor #(MFB_ITEM_WIDTH)::get_type(),
            "m_env_rx_mfb.m_logic_vector_array_agent.m_sequencer",
            this
        );

        // ------------------------- //
        // Environment configuration //
        // ------------------------- //

        // Reset
        m_config_reset                = new;
        m_config_reset.active         = UVM_ACTIVE;
        m_config_reset.interface_name = "vif_reset";
        uvm_config_db #(uvm_reset::config_item)::set(this, "m_reset", "m_config", m_config_reset);
        m_reset = uvm_reset::agent::type_id::create("m_reset", this);

        // RX MFB
        m_config_rx_mfb                = new;
        m_config_rx_mfb.active         = UVM_ACTIVE;
        m_config_rx_mfb.interface_name = "vif_rx_mfb";
        uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, "m_env_rx_mfb", "m_config", m_config_rx_mfb);
        m_env_rx_mfb = uvm_logic_vector_array_mfb::env_rx #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0)::type_id::create("m_env_rx_mfb", this);

        // RX MVB
        m_config_rx_mvb                = new;
        m_config_rx_mvb.active         = UVM_ACTIVE;
        m_config_rx_mvb.interface_name = "vif_rx_mvb";
        m_config_rx_mvb.coverage       = 1;
        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "m_env_rx_mvb", "m_config", m_config_rx_mvb);
        m_env_rx_mvb = uvm_logic_vector_mvb::env_rx #(MFB_REGIONS, RX_MVB_ITEM_WIDTH)::type_id::create("m_env_rx_mvb", this);

        // TX MFB
        m_config_tx_mfb                = new;
        m_config_tx_mfb.active         = UVM_ACTIVE;
        m_config_tx_mfb.interface_name = "vif_tx_mfb";
        m_config_tx_mfb.meta_behav     = uvm_logic_vector_array_mfb::config_item::META_SOF;
        uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, "m_env_tx_mfb", "m_config", m_config_tx_mfb);
        m_env_tx_mfb = uvm_logic_vector_array_mfb::env_tx #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, USERMETA_WIDTH)::type_id::create("m_env_tx_mfb", this);

        // TX MVB
        m_config_tx_mvb                = new;
        m_config_tx_mvb.active         = UVM_ACTIVE;
        m_config_tx_mvb.interface_name = "vif_tx_mvb";
        m_config_tx_mvb.coverage       = 1;
        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "m_env_tx_mvb", "m_config", m_config_tx_mvb);
        m_env_tx_mvb = uvm_logic_vector_mvb::env_tx #(MFB_REGIONS, USERMETA_WIDTH)::type_id::create("m_env_tx_mvb", this);

        m_scoreboard        = scoreboard        #(MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, PKT_MTU, USERMETA_WIDTH, RX_MVB_ITEM_WIDTH)                     ::type_id::create("m_scoreboard", this);
        m_virtual_sequencer = virtual_sequencer #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, USERMETA_WIDTH, RX_MVB_ITEM_WIDTH)::type_id::create("m_virtual_sequencer", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);

        // ---------------------- //
        // Environment connection //
        // ---------------------- //

        // Reset -> RX MFB
        m_reset.sync_connect(m_env_rx_mfb.reset_sync);
        // Reset -> RX MVB
        m_reset.sync_connect(m_env_rx_mvb.reset_sync);
        // Reset -> TX MFB
        m_reset.sync_connect(m_env_tx_mfb.reset_sync);
        // Reset -> TX MVB
        m_reset.sync_connect(m_env_tx_mvb.reset_sync);

        // RX MFB data -> Scoreboard
        m_env_rx_mfb.analysis_port_data.connect(m_scoreboard.analysis_export_rx_mfb);
        // RX MVB -> Scoreboard
        m_env_rx_mvb.analysis_port.connect(m_scoreboard.analysis_export_rx_mvb);

        // TX MFB -> Scoreboard
        m_env_tx_mfb.analysis_port_data.connect(m_scoreboard.analysis_export_tx_mfb_data);
        m_env_tx_mfb.analysis_port_meta.connect(m_scoreboard.analysis_export_tx_mfb_meta);
        // TX MVB -> Scoreboard
        m_env_tx_mvb.analysis_port.connect(m_scoreboard.analysis_export_tx_mvb);

        // ---------------------------- //
        // Virtual sequencer connection //
        // ---------------------------- //

        m_virtual_sequencer.m_reset  = m_reset.m_sequencer;
        m_virtual_sequencer.m_rx_mvb = m_env_rx_mvb.m_sequencer;
        m_virtual_sequencer.m_tx_mfb = m_env_tx_mfb.m_sequencer;
        m_virtual_sequencer.m_tx_mvb = m_env_tx_mvb.m_sequencer;

        assert($cast(m_virtual_sequencer.m_rx_mfb, m_env_rx_mfb.m_sequencer.m_data))
        else begin
            `uvm_fatal(get_full_name(), $sformatf("\n\tCast failed: %s", m_env_rx_mfb.m_sequencer.m_data.get_full_name()))
        end

        // ------------------ //
        // Mailbox connection //
        // ------------------ //

        uvm_config_db #(mailbox #(int unsigned))::set(this, "m_env_rx_mvb.m_logic_vector_agent.m_sequencer", "frame_lengths", m_virtual_sequencer.m_rx_mfb.frame_lengths);
    endfunction

endclass
