// env.sv: Verification environment dma
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz> 

// SPDX-License-Identifier: BSD-3-Clause

class env#(
    RQ_REGIONS,
    RQ_REGION_SIZE,
    RQ_BLOCK_SIZE,
    RQ_ITEM_WIDTH,
    RQ_META_WIDTH,
    RC_REGIONS,
    RC_REGION_SIZE,
    RC_BLOCK_SIZE,
    RC_ITEM_WIDTH,
    RC_META_WIDTH)  extends uvm_env;
    `uvm_component_param_utils(uvm_dma::env#(RQ_REGIONS, RQ_REGION_SIZE, RQ_BLOCK_SIZE, RQ_ITEM_WIDTH, RQ_META_WIDTH, RC_REGIONS, RC_REGION_SIZE, RC_BLOCK_SIZE, RC_ITEM_WIDTH, RC_META_WIDTH));

    localparam DMA_UPHDR_WIDTH   = sv_dma_bus_pack::DMA_UPHDR_WIDTH;
    localparam DMA_DOWNHDR_WIDTH = sv_dma_bus_pack::DMA_DOWNHDR_WIDTH;

    uvm_analysis_port #(uvm_dma::sequence_item_rc) rc_analysis_port;
    uvm_analysis_port #(uvm_dma::sequence_item_rq) rq_analysis_port;

    sequencer m_sequencer;
    uvm_reset::sync_cbs reset_sync;

    protected monitor   m_monitor;
    protected driver    m_driver; 

    protected uvm_logic_vector_array_mfb::env_rx #(RQ_REGIONS, RQ_REGION_SIZE, RQ_BLOCK_SIZE, RQ_ITEM_WIDTH, RQ_META_WIDTH)     m_rq_mfb_env;
    protected uvm_logic_vector_mvb::env_rx #(RQ_REGIONS, DMA_UPHDR_WIDTH)                                                       m_rq_mvb_env;
    /*protected*/ uvm_logic_vector_array_mfb::env_tx #(RC_REGIONS, RC_REGION_SIZE, RC_BLOCK_SIZE, RC_ITEM_WIDTH, RC_META_WIDTH) m_rc_mfb_env;
    /*protected*/ uvm_logic_vector_mvb::env_tx #(RC_REGIONS, DMA_DOWNHDR_WIDTH)                                                 m_rc_mvb_env;

    protected req_fifo#(uvm_logic_vector_array::sequence_item#(32))  fifo_rq_mfb_data;
    protected req_fifo#(uvm_logic_vector::sequence_item#(DMA_UPHDR_WIDTH)) fifo_rq_mvb;
    protected config_item m_config;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);

        fifo_rq_mfb_data = new();
        fifo_rq_mvb      = new();
        reset_sync       = new();
    endfunction

    function void build_phase(uvm_phase phase);
        uvm_logic_vector_array_mfb::config_item  m_rq_mfb_cfg;
        uvm_logic_vector_mvb::config_item        m_rq_mvb_cfg;
        uvm_logic_vector_array_mfb::config_item  m_rc_mfb_cfg;
        uvm_logic_vector_mvb::config_item        m_rc_mvb_cfg;

        super.build_phase(phase);

        if(!uvm_config_db #(config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(this.get_full_name(), "Unable to get configuration object")
        end

        m_rq_mfb_cfg = new();
        m_rq_mfb_cfg.active = UVM_ACTIVE;
        m_rq_mfb_cfg.interface_name    = m_config.interface_name_rq_mfb;
        m_rq_mfb_cfg.meta_behav = uvm_logic_vector_array_mfb::config_item::META_NONE;
        //m_rq_mfb_cfg.meta_behav = (IS_INTEL_DEV) ? uvm_logic_vector_array_mfb::config_item::META_SOF : uvm_logic_vector_array_mfb::config_item::META_NONE;
        m_rq_mfb_cfg.seq_type = "PCIE";
        m_rq_mfb_cfg.seq_cfg  = new();
        m_rq_mfb_cfg.seq_cfg.straddling_set(1);
        uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, "m_rq_mfb_env", "m_config", m_rq_mfb_cfg);
        m_rq_mfb_env = uvm_logic_vector_array_mfb::env_rx #(RQ_REGIONS, RQ_REGION_SIZE, RQ_BLOCK_SIZE, RQ_ITEM_WIDTH, RQ_META_WIDTH)::type_id::create("m_rq_mfb_env", this);

        m_rq_mvb_cfg = new();
        m_rq_mvb_cfg.active = UVM_ACTIVE;
        m_rq_mvb_cfg.interface_name    = m_config.interface_name_rq_mvb;
        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "m_rq_mvb_env", "m_config", m_rq_mvb_cfg);
        m_rq_mvb_env = uvm_logic_vector_mvb::env_rx #(RQ_REGIONS, DMA_UPHDR_WIDTH)::type_id::create("m_rq_mvb_env", this);

        m_rc_mfb_cfg = new();
        m_rc_mfb_cfg.active = UVM_ACTIVE;
        m_rc_mfb_cfg.interface_name    = m_config.interface_name_rc_mfb;
        m_rc_mfb_cfg.meta_behav = uvm_logic_vector_array_mfb::config_item::META_NONE;
        m_rc_mfb_cfg.seq_type = "PCIE";
        m_rc_mfb_cfg.seq_cfg  = new();
        m_rc_mfb_cfg.seq_cfg.straddling_set(1);
        uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, "m_rc_mfb_env", "m_config", m_rc_mfb_cfg);
        m_rc_mfb_env = uvm_logic_vector_array_mfb::env_tx #(RC_REGIONS, RC_REGION_SIZE, RC_BLOCK_SIZE, RC_ITEM_WIDTH, RC_META_WIDTH)::type_id::create("m_rc_mfb_env", this);

        m_rc_mvb_cfg = new();
        m_rc_mvb_cfg.active = UVM_ACTIVE;
        m_rc_mvb_cfg.interface_name    = m_config.interface_name_rc_mvb;
        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "m_rc_mvb_env", "m_config", m_rc_mvb_cfg);
        m_rc_mvb_env = uvm_logic_vector_mvb::env_tx #(RC_REGIONS, DMA_DOWNHDR_WIDTH)::type_id::create("m_rc_mvb_env", this);

        m_sequencer = sequencer::type_id::create("m_sequencer", this);
        m_monitor   = monitor::type_id::create("m_monitor", this);
        m_driver    = driver   ::type_id::create("m_driver", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);

        m_driver.seq_item_port.connect(m_sequencer.seq_item_export);

        uvm_config_db #(req_fifo#(uvm_logic_vector_array::sequence_item#(32)) )::set(m_rq_mfb_env.m_sequencer.m_data, "", "fifo", fifo_rq_mfb_data);
        uvm_config_db #(req_fifo#(uvm_logic_vector::sequence_item#(DMA_UPHDR_WIDTH)))::set(m_rq_mvb_env.m_sequencer       , "", "fifo"     , fifo_rq_mvb);
        uvm_config_db #(req_fifo#(uvm_logic_vector_array::sequence_item#(32)) )::set(this, "m_driver", "fifo_rq_mfb_data", fifo_rq_mfb_data);
        uvm_config_db #(req_fifo#(uvm_logic_vector::sequence_item#(DMA_UPHDR_WIDTH)))::set(this, "m_driver", "fifo_rq_mvb"     , fifo_rq_mvb);

        rc_analysis_port = m_monitor.rc_analysis_port;
        rq_analysis_port = m_monitor.rq_analysis_port;
        rc_analysis_port.connect(m_sequencer.fifo_rsp.analysis_export);

        m_rc_mfb_env.analysis_port_data.connect(m_monitor.rc_mfb.analysis_export);
        m_rc_mvb_env.analysis_port     .connect(m_monitor.rc_mvb.analysis_export);
        m_rq_mfb_env.analysis_port_data.connect(m_monitor.rq_mfb.analysis_export);
        m_rq_mvb_env.analysis_port     .connect(m_monitor.rq_mvb.analysis_export);

        reset_sync.push_back(m_rq_mfb_env.reset_sync);
        reset_sync.push_back(m_rq_mvb_env.reset_sync);
        reset_sync.push_back(m_rc_mfb_env.reset_sync);
        reset_sync.push_back(m_rc_mvb_env.reset_sync);
    endfunction

    task run_phase(uvm_phase phase);
        sequence_void#(uvm_logic_vector_array::sequence_item#(32) ) mfb_data_seq;
        sequence_void#(uvm_logic_vector::sequence_item#(DMA_UPHDR_WIDTH)) mvb_seq;

        mfb_data_seq = sequence_void#(uvm_logic_vector_array::sequence_item#(32) )::type_id::create("mfb_data_seq", m_rq_mfb_env.m_sequencer.m_data);
        assert(mfb_data_seq.randomize()) else begin `uvm_fatal(this.get_full_name(), "\n\t Cannot randomize sequence") end
        mvb_seq = sequence_void#(uvm_logic_vector::sequence_item#(DMA_UPHDR_WIDTH))::type_id::create("mvb_seq", m_rq_mvb_env.m_sequencer);
        assert(mvb_seq.randomize()) else begin `uvm_fatal(this.get_full_name(), "\n\t Cannot randomize sequence") end

        fork
            mfb_data_seq.start(m_rq_mfb_env.m_sequencer.m_data);
            mvb_seq     .start(m_rq_mvb_env.m_sequencer);
        join;
    endtask
endclass

