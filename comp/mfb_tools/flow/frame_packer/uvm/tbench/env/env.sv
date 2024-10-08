// env.sv: Verification environment
// Copyright (C) 2024 CESNET z. s. p. o.
// Author:   David Beneš <xbenes52@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

// Environment for functional verification of encode.

class env #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, SPACE_SIZE_MIN_RX, SPACE_SIZE_MAX_RX, SPACE_SIZE_MIN_TX, SPACE_SIZE_MAX_TX, RX_CHANNELS, PKT_MTU, HDR_META_WIDTH) extends uvm_env;
    //MACROS
    `uvm_component_param_utils(uvm_framepacker::env #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, SPACE_SIZE_MIN_RX, SPACE_SIZE_MAX_RX, SPACE_SIZE_MIN_TX, SPACE_SIZE_MAX_TX, RX_CHANNELS, PKT_MTU, HDR_META_WIDTH));

    /////////////////////////////////////////////////////
    //             COMPONENT DECLARATION               //
    /////////////////////////////////////////////////////
    //<package_name>::<class_name> #(parameters) object_name

    //MFB interface - uvm_logic_vector_array
    protected uvm_logic_vector_array_mfb::env_rx #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0) mfb_rx_env;
    protected uvm_logic_vector_array_mfb::env_tx #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0) mfb_tx_env;

    //MVB_interface - uvm_logic_vector_mvb
    protected uvm_logic_vector_mvb::env_rx #(MFB_REGIONS, $clog2(RX_CHANNELS) + $clog2(PKT_MTU+1))                  mvb_rx_env;
    protected uvm_logic_vector_mvb::env_tx #(MFB_REGIONS, $clog2(RX_CHANNELS) + $clog2(PKT_MTU+1) + HDR_META_WIDTH + 1) mvb_tx_env;

    //Internal signals from shifter
    protected uvm_logic_vector_mvb::env_tx #(1, 2) m_flow_ctrl[RX_CHANNELS];

    //MFB interface - Verification
    protected uvm_logic_vector_array::agent#(MFB_ITEM_WIDTH) m_byte_array_agent;

    //MVB interface - Verification
    protected uvm_meta::agent #(PKT_MTU, RX_CHANNELS, HDR_META_WIDTH) m_info;

    //Data generator
    protected uvm_framepacker::generator #(PKT_MTU, RX_CHANNELS, HDR_META_WIDTH, MFB_ITEM_WIDTH) m_generator;

    //Scoreboard
    scoreboard #(RX_CHANNELS, PKT_MTU, HDR_META_WIDTH,  MFB_ITEM_WIDTH) m_scoreboard;

    //Virtual sequencer
    uvm_framepacker::virt_sequencer#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, PKT_MTU, RX_CHANNELS, HDR_META_WIDTH) vscr;

    //Reset
    uvm_reset::agent m_reset;

    /////////////////////////////////////////////////////
    //          CONSTRUCTOR OF ENVIRONMENT             //
    /////////////////////////////////////////////////////
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    /////////////////////////////////////////////////////
    //                 BUILD PHASE                     //
    /////////////////////////////////////////////////////
    function void build_phase(uvm_phase phase);
        uvm_logic_vector_array_mfb::config_item mfb_cfg_rx;
        uvm_logic_vector_array_mfb::config_item mfb_cfg_tx;
        uvm_logic_vector_mvb::config_item       mvb_cfg_rx;
        uvm_logic_vector_mvb::config_item       mvb_cfg_tx;
        uvm_logic_vector_array::config_item     m_byte_array_agent_cfg;
        uvm_meta::config_item                   m_config_info;
        uvm_reset::config_item                  m_config_reset;
        uvm_logic_vector_mvb::config_item       m_flow_ctrl_cfg[RX_CHANNELS];

        //MFB interface - configuration
            //RX
            mfb_cfg_rx                = new;
            mfb_cfg_rx.active         = UVM_ACTIVE;
            mfb_cfg_rx.interface_name = "vif_mfb_rx";
            mfb_cfg_rx.meta_behav     = uvm_logic_vector_array_mfb::config_item::META_SOF;
            mfb_cfg_rx.seq_cfg        = new();
            mfb_cfg_rx.seq_cfg.space_size_set(SPACE_SIZE_MIN_RX, SPACE_SIZE_MAX_RX);
            //SRC_RDY high probability
            mfb_cfg_rx.seq_cfg.probability_set(0,100);
            uvm_config_db#(uvm_logic_vector_array_mfb::config_item)::set(this, "mfb_rx_env", "m_config", mfb_cfg_rx);

            //TX
            mfb_cfg_tx                = new;
            mfb_cfg_tx.active         = UVM_ACTIVE;
            mfb_cfg_tx.interface_name = "vif_mfb_tx";
            mfb_cfg_tx.meta_behav     = uvm_logic_vector_array_mfb::config_item::META_NONE;
            mfb_cfg_tx.seq_cfg        = new();
            mfb_cfg_tx.seq_cfg.space_size_set(SPACE_SIZE_MIN_TX, SPACE_SIZE_MAX_TX);
            uvm_config_db#(uvm_logic_vector_array_mfb::config_item)::set(this, "mfb_tx_env", "m_config", mfb_cfg_tx);

        //MVB interface - configuration
            //RX
            mvb_cfg_rx                = new;
            mvb_cfg_rx.active         = UVM_ACTIVE;
            mvb_cfg_rx.interface_name = "vif_mvb_rx";
            mvb_cfg_rx.seq_cfg        = new();
            mvb_cfg_rx.seq_cfg.space_size_set(SPACE_SIZE_MIN_RX, SPACE_SIZE_MAX_RX);
            uvm_config_db#(uvm_logic_vector_mvb::config_item)::set(this, "mvb_rx_env", "m_config", mvb_cfg_rx);

            //TX
            mvb_cfg_tx                = new;
            mvb_cfg_tx.active         = UVM_ACTIVE;
            mvb_cfg_tx.interface_name = "vif_mvb_tx";
            mvb_cfg_tx.seq_cfg        = new();
            mvb_cfg_tx.seq_cfg.space_size_set(SPACE_SIZE_MIN_TX, SPACE_SIZE_MAX_TX);
            uvm_config_db#(uvm_logic_vector_mvb::config_item)::set(this, "mvb_tx_env", "m_config", mvb_cfg_tx);

            //Flow Control unit
            for (int unsigned it = 0; it < RX_CHANNELS; it++) begin
                m_flow_ctrl_cfg[it]                 = new;
                m_flow_ctrl_cfg[it].active          = UVM_PASSIVE;
                m_flow_ctrl_cfg[it].interface_name  = $sformatf("vif_mvb_flow_ctrl_%0d", it);
                uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, $sformatf("m_flow_ctrl_%0d", it), "m_config", m_flow_ctrl_cfg[it]);
            end


        //MFB interface - verification configuration
        m_byte_array_agent_cfg        = new();
        m_byte_array_agent_cfg.active = UVM_ACTIVE;
        uvm_config_db #(uvm_logic_vector_array::config_item)::set(this, "m_byte_array_agent", "m_config", m_byte_array_agent_cfg);

        //MVB interface - verification configuration
        m_config_info                 = new;
        m_config_info.active          = UVM_ACTIVE;
        uvm_config_db#(uvm_meta::config_item)::set(this, "m_info", "m_config", m_config_info);

        //RESET configuration setting
        m_config_reset                = new;
        m_config_reset.active         = UVM_ACTIVE;
        m_config_reset.interface_name = "vif_reset";
        uvm_config_db#(uvm_reset::config_item)::set(this, "m_reset", "m_config", m_config_reset);

        //Build of components
        mfb_rx_env         = uvm_logic_vector_array_mfb::env_rx #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0)::type_id::create("mfb_rx_env", this);
        mfb_tx_env         = uvm_logic_vector_array_mfb::env_tx #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0)::type_id::create("mfb_tx_env", this);
        mvb_rx_env         = uvm_logic_vector_mvb::env_rx #(MFB_REGIONS, $clog2(RX_CHANNELS) + $clog2(PKT_MTU+1))::type_id::create("mvb_rx_env", this);
        mvb_tx_env         = uvm_logic_vector_mvb::env_tx #(MFB_REGIONS, $clog2(RX_CHANNELS) + $clog2(PKT_MTU+1) + HDR_META_WIDTH + 1)::type_id::create("mvb_tx_env", this);
        m_byte_array_agent = uvm_logic_vector_array::agent#(MFB_ITEM_WIDTH)::type_id::create("m_byte_array_agent", this);
        m_info             = uvm_meta::agent#(PKT_MTU, RX_CHANNELS, HDR_META_WIDTH)::type_id::create("m_info", this);
        m_reset            = uvm_reset::agent::type_id::create("m_reset", this);
        m_generator        = uvm_framepacker::generator #(PKT_MTU, RX_CHANNELS, HDR_META_WIDTH, MFB_ITEM_WIDTH)::type_id::create("m_generator", this);
        m_scoreboard       = scoreboard #(RX_CHANNELS, PKT_MTU, HDR_META_WIDTH,  MFB_ITEM_WIDTH)::type_id::create("m_scoreboard", this);
        vscr               = uvm_framepacker::virt_sequencer#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, PKT_MTU, RX_CHANNELS, HDR_META_WIDTH)::type_id::create("mfb_vscr",this);
        for (int unsigned it = 0; it < RX_CHANNELS; it++) begin
            m_flow_ctrl[it] = uvm_logic_vector_mvb::env_tx #(1, 2)::type_id::create($sformatf("m_flow_ctrl_%0d", it), this);
        end

    endfunction

    /////////////////////////////////////////////////////
    //                  CONNECT PHASE                  //
    /////////////////////////////////////////////////////
    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);

        //MVB data contain information about channel
        //Connect RX environment
        mfb_rx_env.analysis_port_data.connect(m_scoreboard.analysis_imp_mfb_rx_data);
        mvb_rx_env.analysis_port.connect(m_scoreboard.analysis_imp_mvb_rx);

        //Connect TX environment
        //Meter
        mfb_tx_env.analysis_port_data.connect(m_scoreboard.analysis_imp_mfb_tx_data);

        //Model
        mfb_tx_env.analysis_port_data.connect(m_scoreboard.data_cmp.analysis_imp_dut);

        // MVB
        mvb_tx_env.analysis_port.connect(m_scoreboard.analysis_imp_mvb_tx);

        for (int unsigned i = 0; i < RX_CHANNELS; i++) begin
            m_flow_ctrl[i].analysis_port.connect(m_scoreboard.m_model.analysis_export_flow_ctrl[i].analysis_export);
        end

        //RESET
        m_reset.sync_connect(mfb_rx_env.reset_sync);
        m_reset.sync_connect(mfb_tx_env.reset_sync);
        m_reset.sync_connect(mvb_rx_env.reset_sync);
        m_reset.sync_connect(mvb_tx_env.reset_sync);

        //Virtual sequencer
        vscr.m_mfb_tx_sqr   = mfb_tx_env.m_sequencer;
        vscr.m_mvb_tx_sqr   = mvb_tx_env.m_sequencer;
        vscr.m_mfb_data_sqr = m_byte_array_agent.m_sequencer;
        vscr.m_info         = m_info.m_sequencer;
        vscr.m_reset        = m_reset.m_sequencer;

        //Data generator
        m_generator.seq_item_port_byte_array.connect(m_byte_array_agent.m_sequencer.seq_item_export);
        m_generator.seq_item_port_info.connect(m_info.m_sequencer.seq_item_export);
    endfunction

    /////////////////////////////////////////////////////
    //                     RUN PHASE                   //
    /////////////////////////////////////////////////////
    virtual task run_phase(uvm_phase phase);
        sequence_mfb_data #(MFB_ITEM_WIDTH) mfb_data_seq;
        sequence_mvb_data #($clog2(RX_CHANNELS) + $clog2(PKT_MTU+1)) mvb_data_seq;

        mfb_data_seq           = sequence_mfb_data #(MFB_ITEM_WIDTH)::type_id::create("mfb_data_seq", this);
        mfb_data_seq.tr_export = m_generator.byte_array_export;
        mfb_data_seq.randomize();

        mvb_data_seq           = sequence_mvb_data #($clog2(RX_CHANNELS) + $clog2(PKT_MTU+1))::type_id::create("mvb_data_seq", this);
        mvb_data_seq.tr_export = m_generator.logic_vector_export;
        mvb_data_seq.randomize();

        //Start the sequence on wanted destination
        fork
            mfb_data_seq.start(mfb_rx_env.m_sequencer.m_data);
            // mfb_data_seq.start(mfb_rx_env.m_sequencer.m_meta);
            mvb_data_seq.start(mvb_rx_env.m_sequencer);
        join_none
    endtask

endclass
