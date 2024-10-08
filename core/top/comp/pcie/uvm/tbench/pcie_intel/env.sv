// env.sv: environment for convert PCIE for intel device
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class env #(
    CQ_MFB_REGIONS,
    CQ_MFB_REGION_SIZE,
    CQ_MFB_BLOCK_SIZE,
    AVST_DOWN_META_W,

    CC_MFB_REGIONS,
    CC_MFB_REGION_SIZE,
    CC_MFB_BLOCK_SIZE,
    AVST_UP_META_W
) extends uvm_pcie::env;
    `uvm_component_param_utils(uvm_pcie_intel::env#(
            CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, AVST_DOWN_META_W,
            CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, AVST_UP_META_W));

    localparam ITEM_WIDTH = 32;

    protected uvm_logic_vector_array_avst::env_rx #(CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, ITEM_WIDTH, AVST_DOWN_META_W, 30) m_avst_down;
    protected uvm_logic_vector_array_avst::env_tx #(CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, ITEM_WIDTH, AVST_UP_META_W, 3)    m_avst_up;

    protected req_fifo#(uvm_pcie::header) fifo_data;
    protected req_fifo#(uvm_pcie::header) fifo_meta;


    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        fifo_data = new();
        fifo_meta = new();
    endfunction


    function void build_phase(uvm_phase phase);
        uvm_pcie::config_item  m_config;

        uvm_logic_vector_array_avst::config_item m_up_cfg;
        uvm_logic_vector_array_avst::config_item m_down_cfg;

        if(!uvm_config_db #(uvm_pcie::config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(this.get_full_name(), "\n\tUnable to get configuration object");
        end

        uvm_pcie::monitor::type_id::set_inst_override(uvm_pcie_intel::monitor#(AVST_UP_META_W, AVST_DOWN_META_W)::get_type(),
            {this.get_full_name(), ".m_monitor"});

        uvm_pcie::driver::type_id::set_inst_override(uvm_pcie_intel::driver::get_type(),
            {this.get_full_name(), ".m_driver"});


        super.build_phase(phase);

        m_up_cfg   = new();
        m_up_cfg.active         = UVM_ACTIVE;
        m_up_cfg.interface_name = {m_config.interface_name, "_down"};
        m_up_cfg.meta_behav     = uvm_logic_vector_array_avst::config_item::META_SOF;
        m_up_cfg.seq_cfg        = new();
        m_up_cfg.seq_cfg.straddling_set(1);
        uvm_config_db #(uvm_logic_vector_array_avst::config_item)::set(this, "m_avst_down", "m_config", m_up_cfg);
        m_avst_down = uvm_logic_vector_array_avst::env_rx #(CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, ITEM_WIDTH, AVST_DOWN_META_W, 30)::type_id::create("m_avst_down", this);

        m_down_cfg = new();
        m_down_cfg.active         = UVM_ACTIVE;
        m_down_cfg.interface_name = {m_config.interface_name, "_up"};
        m_down_cfg.meta_behav     = uvm_logic_vector_array_avst::config_item::META_SOF;
        m_down_cfg.seq_cfg        = new();
        m_down_cfg.seq_cfg.straddling_set(1);
        uvm_config_db #(uvm_logic_vector_array_avst::config_item)::set(this, "m_avst_up", "m_config", m_down_cfg);
        m_avst_up   = uvm_logic_vector_array_avst::env_tx #(CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, ITEM_WIDTH, AVST_UP_META_W, 3)::type_id::create("m_avst_up", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        uvm_pcie_intel::monitor#(AVST_UP_META_W, AVST_DOWN_META_W) x_mon;

        super.connect_phase(phase);

        if($cast(x_mon, m_monitor)) begin
            m_avst_up.analysis_port_meta.connect  (x_mon.avalon_up_meta.analysis_export);
            m_avst_up.analysis_port_data.connect  (x_mon.avalon_up_data.analysis_export);
            m_avst_down.analysis_port_meta.connect(x_mon.avalon_down_meta.analysis_export);
            m_avst_down.analysis_port_data.connect(x_mon.avalon_down_data.analysis_export);
        end else begin
            `uvm_fatal(this.get_full_name(), "\n\tCannot cast to pcie_xilinx monitor");
        end

        reset_sync.push_back(m_avst_up.reset_sync);
        reset_sync.push_back(m_avst_down.reset_sync);

        //connect pcie driver with xilinx sequence
        uvm_config_db #(req_fifo#(uvm_pcie::header))::set(m_avst_down.m_sequencer.m_data, "", "seq_fifo", fifo_data);
        uvm_config_db #(req_fifo#(uvm_pcie::header))::set(m_avst_down.m_sequencer.m_meta, "", "seq_fifo", fifo_meta);
        uvm_config_db #(req_fifo#(uvm_pcie::header))::set(this, "m_driver", "seq_fifo_data", fifo_data);
        uvm_config_db #(req_fifo#(uvm_pcie::header))::set(this, "m_driver", "seq_fifo_meta", fifo_meta);
    endfunction

    task run_phase(uvm_phase phase);
        uvm_pcie_intel::sequence_data                    seq_data;
        uvm_pcie_intel::sequence_meta#(AVST_DOWN_META_W) seq_meta;
        uvm_avst::sequence_lib_tx#(CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, ITEM_WIDTH, AVST_UP_META_W) seq_up_rdy;

        seq_data = uvm_pcie_intel::sequence_data::type_id::create("seq_data", this);
        assert(seq_data.randomize()) else begin `uvm_fatal(this.get_full_name(), "\n\t Cannot randomize sequence") end
        seq_meta = uvm_pcie_intel::sequence_meta#(AVST_DOWN_META_W)::type_id::create("seq_meta", this);
        assert(seq_meta.randomize()) else begin `uvm_fatal(this.get_full_name(), "\n\t Cannot randomize sequence") end



        seq_up_rdy = uvm_avst::sequence_lib_tx#(CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, ITEM_WIDTH, AVST_UP_META_W)::type_id::create("seq_up_rdy", this);
        seq_up_rdy.init_sequence();
        seq_up_rdy.min_random_count = 100;
        seq_up_rdy.max_random_count = 200;

        fork
            seq_data.start(m_avst_down.m_sequencer.m_data);
            seq_meta.start(m_avst_down.m_sequencer.m_meta);

            forever begin
                assert(seq_up_rdy.randomize());
                seq_up_rdy.start(m_avst_up.m_sequencer);
            end
        join;
    endtask

endclass
