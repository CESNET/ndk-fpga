// env.sv: Verification environment
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
// SPDX-License-Identifier: BSD-3-Clause

// Components:
//   m_env_rx     - active MFB RX agent (data + {META, TS})
//   m_env_tx     - passive MFB TX agent (DST_RDY is tied high in the testbench)
//   m_reset      - DUT RESET
//   m_time_reset - DUT TIME_RESET
//   m_scoreboard - reference model + time-aware comparers
//   vscr         - virtual sequencer used by the test sequences
class env #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned BLOCK_SIZE,
    int unsigned ITEM_WIDTH,
    int unsigned META_WIDTH,
    int unsigned EXTENDED_META_WIDTH,
    int unsigned TS_WIDTH,
    int unsigned TS_FORMAT,
    time         CLK_PERIOD,
    int unsigned PIPE_LAT,
    int unsigned ARRIV_LAT,
    int unsigned GAP_TIME
) extends uvm_env;
    `uvm_component_param_utils(uvm_packet_delayer::env #(
        REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, EXTENDED_META_WIDTH, TS_WIDTH, TS_FORMAT,
        CLK_PERIOD, PIPE_LAT, ARRIV_LAT, GAP_TIME))

    // RX stimulus pacing, can be overridden through the config DB
    // ("rx_space_size_min/max", "rx_rdy_probability_min/max").
    //
    // The default keeps the gap between packets well below the smallest
    // timestamp step, so packets arrive before their predecessor's timestamp
    // elapses and the DUT really has to hold them (release is timestamp driven,
    // not arrival driven). The almost-full test floods at space 0 / rdy 100 %.
    int unsigned RX_SPACE_SIZE_MIN      = 0;
    int unsigned RX_SPACE_SIZE_MAX      = 3;
    int unsigned RX_RDY_PROBABILITY_MIN = 95;
    int unsigned RX_RDY_PROBABILITY_MAX = 100;

    uvm_logic_vector_array_mfb::env_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, EXTENDED_META_WIDTH) m_env_rx;
    uvm_logic_vector_array_mfb::env_tx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) m_env_tx;
    uvm_logic_vector_array_mfb::config_item m_mfb_rx_config;
    uvm_logic_vector_array_mfb::config_item m_mfb_tx_config;

    uvm_reset::agent       m_reset;
    uvm_reset::config_item m_reset_config;

    uvm_reset::agent       m_time_reset;
    uvm_reset::config_item m_time_reset_config;

    uvm_packet_delayer::virtual_sequencer #(ITEM_WIDTH, EXTENDED_META_WIDTH) vscr;

    uvm_packet_delayer::scoreboard #(
        ITEM_WIDTH, META_WIDTH, EXTENDED_META_WIDTH, TS_WIDTH, TS_FORMAT, CLK_PERIOD,
        PIPE_LAT, ARRIV_LAT, GAP_TIME
    ) m_scoreboard;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        void'(uvm_config_db#(int unsigned)::get(this, "", "rx_space_size_min",      RX_SPACE_SIZE_MIN));
        void'(uvm_config_db#(int unsigned)::get(this, "", "rx_space_size_max",      RX_SPACE_SIZE_MAX));
        void'(uvm_config_db#(int unsigned)::get(this, "", "rx_rdy_probability_min", RX_RDY_PROBABILITY_MIN));
        void'(uvm_config_db#(int unsigned)::get(this, "", "rx_rdy_probability_max", RX_RDY_PROBABILITY_MAX));

        // RX: active, paced arrivals
        m_mfb_rx_config                = new;
        m_mfb_rx_config.active         = UVM_ACTIVE;
        m_mfb_rx_config.interface_name = "vif_rx";
        m_mfb_rx_config.meta_behav     = uvm_logic_vector_array_mfb::config_item::META_SOF;
        m_mfb_rx_config.seq_cfg.space_size_set(RX_SPACE_SIZE_MIN, RX_SPACE_SIZE_MAX);
        m_mfb_rx_config.seq_cfg.probability_set(RX_RDY_PROBABILITY_MIN, RX_RDY_PROBABILITY_MAX);
        uvm_config_db#(uvm_logic_vector_array_mfb::config_item)::set(this, "m_env_rx", "m_config", m_mfb_rx_config);

        // TX: passive (only monitors)
        m_mfb_tx_config                = new;
        m_mfb_tx_config.active         = UVM_PASSIVE;
        m_mfb_tx_config.interface_name = "vif_tx";
        m_mfb_tx_config.meta_behav     = uvm_logic_vector_array_mfb::config_item::META_SOF;
        uvm_config_db#(uvm_logic_vector_array_mfb::config_item)::set(this, "m_env_tx", "m_config", m_mfb_tx_config);

        m_reset_config                = new;
        m_reset_config.active         = UVM_ACTIVE;
        m_reset_config.interface_name = "vif_reset";
        uvm_config_db#(uvm_reset::config_item)::set(this, "m_reset", "m_config", m_reset_config);

        m_time_reset_config                = new;
        m_time_reset_config.active         = UVM_ACTIVE;
        m_time_reset_config.interface_name = "vif_time_reset";
        uvm_config_db#(uvm_reset::config_item)::set(this, "m_time_reset", "m_config", m_time_reset_config);

        m_env_rx = uvm_logic_vector_array_mfb::env_rx #(
            REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, EXTENDED_META_WIDTH
        )::type_id::create("m_env_rx", this);
        m_env_tx = uvm_logic_vector_array_mfb::env_tx #(
            REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH
        )::type_id::create("m_env_tx", this);

        m_reset      = uvm_reset::agent::type_id::create("m_reset", this);
        m_time_reset = uvm_reset::agent::type_id::create("m_time_reset", this);
        vscr = uvm_packet_delayer::virtual_sequencer #(ITEM_WIDTH, EXTENDED_META_WIDTH)::type_id::create("vscr", this);

        m_scoreboard = uvm_packet_delayer::scoreboard #(
            ITEM_WIDTH, META_WIDTH, EXTENDED_META_WIDTH, TS_WIDTH, TS_FORMAT, CLK_PERIOD,
            PIPE_LAT, ARRIV_LAT, GAP_TIME
        )::type_id::create("m_scoreboard", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        // RX -> model, TX -> comparers, TIME_RESET -> model
        m_env_rx.analysis_port_data.connect(m_scoreboard.analysis_imp_mfb_rx_data);
        m_env_rx.analysis_port_meta.connect(m_scoreboard.analysis_imp_mfb_rx_meta);
        m_env_tx.analysis_port_data.connect(m_scoreboard.data_cmp.analysis_imp_dut);
        m_env_tx.analysis_port_meta.connect(m_scoreboard.meta_cmp.analysis_imp_dut);

        vscr.m_reset_sqr      = m_reset.m_sequencer;
        vscr.m_time_reset_sqr = m_time_reset.m_sequencer;
        vscr.m_mfb_data_sqr   = m_env_rx.m_sequencer.m_data;
        vscr.m_mfb_meta_sqr   = m_env_rx.m_sequencer.m_meta;

        m_reset.sync_connect(m_env_rx.reset_sync);
        m_reset.sync_connect(m_scoreboard.m_model.reset_sync);
        m_time_reset.sync_connect(m_scoreboard.m_model.time_reset_sync_i);
    endfunction
endclass
