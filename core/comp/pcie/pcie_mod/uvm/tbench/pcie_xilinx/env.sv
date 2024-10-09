// env.sv: Convert PCIE to xilinx device interface
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class env #(
     CQ_REGIONS,
     CQ_REGION_SIZE,
     CQ_BLOCK_SIZE,
     CQ_USER_WIDTH,

     CC_REGIONS,
     CC_REGION_SIZE,
     CC_BLOCK_SIZE,
     CC_USER_WIDTH,

     RQ_REGIONS,
     RQ_REGION_SIZE,
     RQ_BLOCK_SIZE,
     RQ_USER_WIDTH,

     RC_REGIONS,
     RC_REGION_SIZE,
     RC_BLOCK_SIZE,
     RC_USER_WIDTH,

     STRADDLING
) extends uvm_pcie::env;
    `uvm_component_param_utils(uvm_pcie_xilinx::env#(
            CQ_REGIONS, CQ_REGION_SIZE, CQ_BLOCK_SIZE, CQ_USER_WIDTH, CC_REGIONS, CC_REGION_SIZE, CC_BLOCK_SIZE, CC_USER_WIDTH,
            RQ_REGIONS, RQ_REGION_SIZE, RQ_BLOCK_SIZE, RQ_USER_WIDTH, RC_REGIONS, RC_REGION_SIZE, RC_BLOCK_SIZE, RC_USER_WIDTH, STRADDLING));

    localparam ITEM_WIDTH  = 32;

    localparam CQ_DATA_WIDTH  = CQ_REGIONS*CQ_REGION_SIZE*CQ_BLOCK_SIZE*ITEM_WIDTH;
    localparam CC_DATA_WIDTH  = CC_REGIONS*CC_REGION_SIZE*CC_BLOCK_SIZE*ITEM_WIDTH;
    localparam RQ_DATA_WIDTH  = RQ_REGIONS*RQ_REGION_SIZE*RQ_BLOCK_SIZE*ITEM_WIDTH;
    localparam RC_DATA_WIDTH  = RC_REGIONS*RC_REGION_SIZE*RC_BLOCK_SIZE*ITEM_WIDTH;

    localparam RC_STRADDLING = 1;
    localparam RQ_STRADDLING = (RQ_USER_WIDTH == 137) ? 1 : 0;
    // Not yet supported
    localparam CC_STRADDLING = 0;
    localparam CQ_STRADDLING = (CQ_USER_WIDTH == 183 && STRADDLING) ? 1 : 0;


    protected uvm_logic_vector_array_axi::env_rx #(CQ_DATA_WIDTH, CQ_USER_WIDTH, ITEM_WIDTH, CQ_REGIONS, CQ_BLOCK_SIZE, CQ_STRADDLING) m_axi_cq_env;
    protected uvm_logic_vector_array_axi::env_tx #(CC_DATA_WIDTH, CC_USER_WIDTH, ITEM_WIDTH, CC_REGIONS, CC_BLOCK_SIZE, CC_STRADDLING) m_axi_cc_env;
    protected uvm_logic_vector_array_axi::env_tx #(RQ_DATA_WIDTH, RQ_USER_WIDTH, ITEM_WIDTH, RQ_REGIONS, RQ_BLOCK_SIZE, RQ_STRADDLING) m_axi_rq_env;
    protected uvm_logic_vector_array_axi::env_rx #(RC_DATA_WIDTH, RC_USER_WIDTH, ITEM_WIDTH, RC_REGIONS, RC_BLOCK_SIZE, RC_STRADDLING) m_axi_rc_env;

    protected req_fifo#(uvm_pcie::request_header)   fifo_cq;
    protected req_fifo#(uvm_pcie::completer_header) fifo_rc;


    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        fifo_cq = new();
        fifo_rc = new();
    endfunction

    function void build_phase(uvm_phase phase);
        uvm_pcie::config_item                    m_config;
        uvm_logic_vector_array_axi::config_item  m_axi_cq_cfg;
        uvm_logic_vector_array_axi::config_item  m_axi_cc_cfg;
        uvm_logic_vector_array_axi::config_item  m_axi_rc_cfg;
        uvm_logic_vector_array_axi::config_item  m_axi_rq_cfg;

        if(!uvm_config_db #(uvm_pcie::config_item)::get(this, "", "m_config", m_config)) begin
            `uvm_fatal(this.get_full_name(), "\n\tUnable to get configuration object");
        end

        uvm_pcie::monitor::type_id::set_inst_override(uvm_pcie_xilinx::monitor::get_type(),
            {this.get_full_name(), ".m_monitor"});

        uvm_pcie::driver::type_id::set_inst_override(uvm_pcie_xilinx::driver::get_type(),
            {this.get_full_name(), ".m_driver"});

        super.build_phase(phase);


        m_axi_cq_cfg                = new();
        m_axi_cq_cfg.active         = m_config.active;
        m_axi_cq_cfg.meta_behav     = uvm_logic_vector_array_axi::config_item::META_EOF;
        m_axi_cq_cfg.interface_name = {m_config.interface_name, "_cq"};
        uvm_config_db #(uvm_logic_vector_array_axi::config_item)::set(this, "m_axi_cq_env", "m_config", m_axi_cq_cfg);
        m_axi_cq_env = uvm_logic_vector_array_axi::env_rx #(CQ_DATA_WIDTH, CQ_USER_WIDTH, ITEM_WIDTH, CQ_REGIONS, CQ_BLOCK_SIZE, CQ_STRADDLING)::type_id::create("m_axi_cq_env", this);

        m_axi_cc_cfg                = new();
        m_axi_cc_cfg.active         = m_config.active;
        m_axi_cc_cfg.meta_behav     = uvm_logic_vector_array_axi::config_item::META_EOF;
        m_axi_cc_cfg.interface_name = {m_config.interface_name, "_cc"};
        uvm_config_db #(uvm_logic_vector_array_axi::config_item)::set(this, "m_axi_cc_env", "m_config", m_axi_cc_cfg);
        m_axi_cc_env = uvm_logic_vector_array_axi::env_tx #(CC_DATA_WIDTH, CC_USER_WIDTH, ITEM_WIDTH, CC_REGIONS, CC_BLOCK_SIZE, CC_STRADDLING)::type_id::create("m_axi_cc_env", this);

        m_axi_rc_cfg                = new();
        m_axi_rc_cfg.active         = m_config.active;
        m_axi_rc_cfg.meta_behav     = uvm_logic_vector_array_axi::config_item::META_EOF;
        m_axi_rc_cfg.interface_name = {m_config.interface_name, "_rc"};
        uvm_config_db #(uvm_logic_vector_array_axi::config_item)::set(this, "m_axi_rc_env", "m_config", m_axi_rc_cfg);
        m_axi_rc_env = uvm_logic_vector_array_axi::env_rx #(RC_DATA_WIDTH, RC_USER_WIDTH, ITEM_WIDTH, RC_REGIONS, RC_BLOCK_SIZE, RC_STRADDLING)::type_id::create("m_axi_rc_env", this);

        m_axi_rq_cfg                = new();
        m_axi_rq_cfg.active         = m_config.active;
        m_axi_rq_cfg.meta_behav     = uvm_logic_vector_array_axi::config_item::META_EOF;
        m_axi_rq_cfg.interface_name = {m_config.interface_name, "_rq"};
        uvm_config_db #(uvm_logic_vector_array_axi::config_item)::set(this, "m_axi_rq_env", "m_config", m_axi_rq_cfg);
        m_axi_rq_env = uvm_logic_vector_array_axi::env_tx #(RQ_DATA_WIDTH, RQ_USER_WIDTH, ITEM_WIDTH, RQ_REGIONS, RQ_BLOCK_SIZE, RQ_STRADDLING)::type_id::create("m_axi_rq_env", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        uvm_pcie_xilinx::monitor x_mon;

        super.connect_phase(phase);

        if($cast(x_mon, m_monitor)) begin
            m_axi_rc_env.analysis_port_data.connect(x_mon.axi_rc.analysis_export);
            m_axi_cq_env.analysis_port_data.connect(x_mon.axi_cq.analysis_export);
            m_axi_cc_env.analysis_port_data.connect(x_mon.axi_cc.analysis_export);
            m_axi_rq_env.analysis_port_data.connect(x_mon.axi_rq.analysis_export);
        end else begin
            `uvm_fatal(this.get_full_name(), "\n\tCannot cast to pcie_xilinx monitor");
        end

        reset_sync.push_back(m_axi_cq_env.reset_sync);
        reset_sync.push_back(m_axi_cc_env.reset_sync);
        reset_sync.push_back(m_axi_rc_env.reset_sync);
        reset_sync.push_back(m_axi_rq_env.reset_sync);

        //connect pcie driver with xilinx sequence
        uvm_config_db #(req_fifo#(uvm_pcie::request_header)  )::set(m_axi_cq_env.m_sequencer.m_data, "", "seq_fifo_cq", fifo_cq);
        uvm_config_db #(req_fifo#(uvm_pcie::completer_header))::set(m_axi_rc_env.m_sequencer.m_data, "", "seq_fifo_rc", fifo_rc);
        uvm_config_db #(req_fifo#(uvm_pcie::request_header)  )::set(this, "m_driver", "seq_fifo_cq", fifo_cq);
        uvm_config_db #(req_fifo#(uvm_pcie::completer_header))::set(this, "m_driver", "seq_fifo_rc", fifo_rc);
    endfunction

    task run_phase(uvm_phase phase);
        uvm_pcie_xilinx::sequence_cq seq_cq;
        uvm_pcie_xilinx::sequence_rc seq_rc;
        uvm_axi::sequence_lib_tx #(CC_DATA_WIDTH, CC_USER_WIDTH, CC_REGIONS) m_axi_cc_lib;
        uvm_axi::sequence_lib_tx #(RQ_DATA_WIDTH, RQ_USER_WIDTH, RQ_REGIONS) m_axi_rq_lib;


        seq_cq = uvm_pcie_xilinx::sequence_cq::type_id::create("seq_cq", this);
        assert(seq_cq.randomize()) else begin `uvm_fatal(this.get_full_name(), "\n\t Cannot randomize sequence") end
        seq_rc = uvm_pcie_xilinx::sequence_rc::type_id::create("seq_rc", this);
        assert(seq_rc.randomize()) else begin `uvm_fatal(this.get_full_name(), "\n\t Cannot randomize sequence") end

        m_axi_cc_lib = uvm_axi::sequence_lib_tx #(CC_DATA_WIDTH, CC_USER_WIDTH, CC_REGIONS)::type_id::create("m_axi_cc_lib", this);
        m_axi_cc_lib.init_sequence();
        m_axi_cc_lib.min_random_count = 100;
        m_axi_cc_lib.max_random_count = 200;

        m_axi_rq_lib = uvm_axi::sequence_lib_tx #(RQ_DATA_WIDTH, RQ_USER_WIDTH, RQ_REGIONS)::type_id::create("m_axi_rq_lib", this);
        m_axi_rq_lib.init_sequence();
        m_axi_rq_lib.min_random_count = 100;
        m_axi_rq_lib.max_random_count = 200;

        fork
            seq_cq.start(m_axi_cq_env.m_sequencer.m_data);
            seq_rc.start(m_axi_rc_env.m_sequencer.m_data);

            forever begin
                assert(m_axi_cc_lib.randomize());
                m_axi_cc_lib.start(m_axi_cc_env.m_sequencer);
            end

            forever begin
                assert(m_axi_rq_lib.randomize());
                m_axi_rq_lib.start(m_axi_rq_env.m_sequencer);
            end

        join;
    endtask
endclass


