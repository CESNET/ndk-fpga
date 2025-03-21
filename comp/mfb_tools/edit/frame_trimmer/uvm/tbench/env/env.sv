// env.sv: Verification environment
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class env #(int unsigned REGIONS, int unsigned REGION_SIZE, int unsigned BLOCK_SIZE, int unsigned ITEM_WIDTH, int unsigned META_WIDTH, int unsigned PKT_MTU) extends uvm_env;
    `uvm_component_param_utils(uvm_mfb_frame_trimmer::env #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, PKT_MTU))

    // Reset environment
    uvm_reset::agent m_reset;

    // RX environments
    uvm_logic_vector_array_mfb::env_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH+1+$clog2(PKT_MTU+1)) m_env_rx_mfb;

    // TX environments
    uvm_logic_vector_array_mfb::env_tx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) m_env_tx_mfb;

    // Scoreboard
    scoreboard #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, PKT_MTU) m_scoreboard;
    // Virtual sequencer
    virtual_sequencer #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, PKT_MTU) m_virtual_sequencer;

    // Constructor
    function new(string name = "env", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        uvm_reset::config_item                  m_config_reset;
        uvm_logic_vector_array_mfb::config_item m_config_rx_mfb;
        uvm_logic_vector_array_mfb::config_item m_config_tx_mfb;

        super.build_phase(phase);

        // ------------------- //
        // Database overriding //
        // ------------------- //

        uvm_logic_vector_array::sequencer #(ITEM_WIDTH)::type_id::set_inst_override(
            sequencer_length_extractor #(ITEM_WIDTH)::get_type(),
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
        m_config_rx_mfb.meta_behav     = uvm_logic_vector_array_mfb::config_item::META_SOF;
        uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, "m_env_rx_mfb", "m_config", m_config_rx_mfb);
        m_env_rx_mfb = uvm_logic_vector_array_mfb::env_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH+1+$clog2(PKT_MTU+1))::type_id::create("m_env_rx_mfb", this);

        // TX MFB
        m_config_tx_mfb                = new;
        m_config_tx_mfb.active         = UVM_ACTIVE;
        m_config_tx_mfb.interface_name = "vif_tx_mfb";
        m_config_tx_mfb.meta_behav     = uvm_logic_vector_array_mfb::config_item::META_SOF;
        uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, "m_env_tx_mfb", "m_config", m_config_tx_mfb);
        m_env_tx_mfb = uvm_logic_vector_array_mfb::env_tx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::type_id::create("m_env_tx_mfb", this);

        m_scoreboard        = scoreboard        #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, PKT_MTU)::type_id::create("m_scoreboard", this);
        m_virtual_sequencer = virtual_sequencer #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, PKT_MTU)::type_id::create("m_virtual_sequencer", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);

        // ---------------------- //
        // Environment connection //
        // ---------------------- //

        // Reset -> RX MFB
        m_reset.sync_connect(m_env_rx_mfb.reset_sync);
        // Reset -> TX MFB
        m_reset.sync_connect(m_env_tx_mfb.reset_sync);

        // RX MFB -> Scoreboard
        m_env_rx_mfb.analysis_port_data.connect(m_scoreboard.analysis_export_rx_mfb_data);
        m_env_rx_mfb.analysis_port_meta.connect(m_scoreboard.analysis_export_rx_mfb_meta);

        // TX MFB -> Scoreboard
        m_env_tx_mfb.analysis_port_data.connect(m_scoreboard.analysis_export_tx_mfb_data);
        m_env_tx_mfb.analysis_port_meta.connect(m_scoreboard.analysis_export_tx_mfb_meta);

        // ---------------------------- //
        // Virtual sequencer connection //
        // ---------------------------- //

        m_virtual_sequencer.m_reset       = m_reset.m_sequencer;
        m_virtual_sequencer.m_rx_mfb_meta = m_env_rx_mfb.m_sequencer.m_meta;
        m_virtual_sequencer.m_tx_mfb      = m_env_tx_mfb.m_sequencer;

        assert($cast(m_virtual_sequencer.m_rx_mfb_data, m_env_rx_mfb.m_sequencer.m_data))
        else begin
            `uvm_fatal(get_full_name(), $sformatf("\n\tCast failed: %s", m_env_rx_mfb.m_sequencer.m_data.get_full_name()))
        end

        uvm_config_db #(mailbox #(int unsigned))::set(this, "m_env_rx_mfb.m_logic_vector_agent.m_sequencer", "mfb_item_lengths", m_virtual_sequencer.m_rx_mfb_data.mfb_item_lengths);
    endfunction

endclass
