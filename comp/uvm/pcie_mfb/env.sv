// env.sv: Verification environment
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class env_rx #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned BLOCK_SIZE,
    direction_t  DIR,
    meta_position_t META_TYPE,
    logic STRADDLING, // TODO: REMOVE STRADDLING it if you want to switch off straddling you shoudld use comb 1, X, REGIONS*y, 32
    device_t DEVICE
) extends uvm_pcie::env_rx;
    `uvm_component_param_utils(uvm_pcie_mfb::env_rx#(REGIONS, REGION_SIZE, BLOCK_SIZE, DIR, META_TYPE, STRADDLING, DEVICE));

    // LOCAL PARAMETERS
    localparam ITEM_WIDTH = 32; //as all pcie devices
    localparam META_WIDTH = (META_TYPE != MFB_META_NONE) ? meta_width_get(DIR, DEVICE) : 0;

    //LOW-LEVEL interface
    protected uvm_logic_vector_array_mfb::env_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) m_lva;
    //protected uvm_logic_vector_mvb::env_rx #(REGIONS, MVB_META_WIDTH)                                            m_mvb;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        //ret |= super.used();
        //ret |= m_avst.used();
        return ret;
    endfunction

    virtual function void bar_register(uvm_pcie::bar_config cfg);
        super.bar_register(cfg);
        m_monitor.bar_register(cfg);
    endfunction

    function void build_phase(uvm_phase phase);
        //uvm_mfb::config_item mfb_cfg;
        uvm_logic_vector_mvb::config_item mvb_cfg;
        uvm_logic_vector_array_mfb::config_item  m_lva_cfg;

        //register driver in factory
        uvm_pcie::monitor::type_id::set_inst_override(monitor_rx#(REGIONS, REGION_SIZE, BLOCK_SIZE, DIR, META_TYPE, DEVICE)::get_type(), "m_monitor", this);
        uvm_pcie::driver::type_id::set_inst_override (driver #(DIR, META_TYPE, DEVICE)                                     ::get_type(), "m_driver", this);


        super.build_phase(phase);

        m_lva_cfg = new();
        m_lva_cfg.interface_name = {m_config.interface_name, "_mfb"};
        m_lva_cfg.active         = m_config.active;
        m_lva_cfg.meta_behav     = uvm_logic_vector_array_mfb::config_item::META_SOF;
        m_lva_cfg.seq_cfg  = new();
        m_lva_cfg.set_pcie(STRADDLING);
        uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, "m_lva", "m_config", m_lva_cfg);
        m_lva = uvm_logic_vector_array_mfb::env_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::type_id::create("m_lva", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        monitor_rx#(REGIONS, REGION_SIZE, BLOCK_SIZE, DIR, META_TYPE, DEVICE) m_monitor_cast;
        driver #(DIR, META_TYPE, DEVICE)                                      m_driver_cast;

        super.connect_phase(phase);

        $cast(m_monitor_cast, m_monitor);
        m_lva.analysis_port_data.connect(m_monitor_cast.port_data.analysis_export);
        if (META_TYPE != MFB_META_NONE) begin
            m_lva.analysis_port_meta.connect(m_monitor_cast.port_meta.analysis_export);
        end

        $cast(m_driver_cast, m_driver);
        uvm_config_db#(uvm_common::fifo#(uvm_logic_vector_array::sequence_item #(32))           )::set(m_lva.m_sequencer.m_data, "" , "in_fifo", m_driver_cast.data_fifo);
        if (META_TYPE != MFB_META_NONE) begin
            uvm_config_db#(uvm_common::fifo#(uvm_logic_vector::sequence_item #(meta_width_get(DIR, DEVICE))))::set(m_lva.m_sequencer.m_meta, "" , "in_fifo", m_driver_cast.meta_fifo);
        end
    endfunction

    task run_phase(uvm_phase phase);
        sequence_data seq_data;
        sequence_meta#(DIR, DEVICE) seq_meta;

        seq_data = sequence_data::type_id::create("seq_data", this);
        seq_meta = sequence_meta#(DIR, DEVICE)::type_id::create("seq_meta", this);

        fork
            forever begin
                assert(seq_data.randomize);
                seq_data.start(m_lva.m_sequencer.m_data);
            end

            forever begin
                assert(seq_meta.randomize);
                if (META_TYPE != MFB_META_NONE) begin
                    seq_meta.start(m_lva.m_sequencer.m_meta);
                end
            end
        join;
    endtask
endclass

class env_mvb_rx #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned BLOCK_SIZE,
    direction_t  DIR,
    meta_position_t META_TYPE,
    logic STRADDLING, // TODO: REMOVE STRADDLING it if you want to switch off straddling you shoudld use comb 1, X, REGIONS*y, 32
    device_t DEVICE
) extends env_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, DIR, MFB_META_NONE, STRADDLING, DEVICE);
    `uvm_component_param_utils(uvm_pcie_mfb::env_mvb_rx#(REGIONS, REGION_SIZE, BLOCK_SIZE, DIR, STRADDLING, DEVICE));
    // LOCAL PARAMETERS
    localparam MVB_META_WIDTH = meta_width_get(DIR, DEVICE);
    //protected uvm_mvb::agent_tx #(REGIONS, MVB_META_WIDTH)                                      m_mvb;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= super.used();
        //ret |= m_avst.used();
        return ret;
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        `uvm_fatal(this.get_full_name(), "\n\tTHIS IS NOT IMPLEMENTED!!\n");
    endfunction
endclass


///////////////////////////////////////////////////////////////
// TX - ENVIRONMENT
///////////////////////////////////////////////////////////////
class env_tx #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned BLOCK_SIZE,
    direction_t  DIR,
    meta_position_t META_TYPE,
    device_t DEVICE
) extends uvm_pcie::env_tx;
    `uvm_component_param_utils(uvm_pcie_mfb::env_tx#(REGIONS, REGION_SIZE, BLOCK_SIZE, DIR, META_TYPE, DEVICE));

    // LOCAL PARAMETERS
    localparam ITEM_WIDTH = 32; //as all pcie devices
    localparam META_WIDTH = (META_TYPE != MFB_META_NONE) ? meta_width_get(DIR, DEVICE) : 0;

    //LOW-LEVEL interface
    protected uvm_mfb::agent_tx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) m_mfb;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        //ret |= super.used();
        //ret |= m_avst.used();
        return ret;
    endfunction

    virtual function void bar_register(uvm_pcie::bar_config cfg);
        super.bar_register(cfg);
        m_monitor.bar_register(cfg);
    endfunction

    function void build_phase(uvm_phase phase);
        uvm_mfb::config_item mfb_cfg;

        //register driver in factory
        uvm_pcie::monitor::type_id::set_inst_override(monitor#(REGIONS, REGION_SIZE, BLOCK_SIZE, DIR, META_TYPE, DEVICE)::get_type(), "m_monitor", this);

        super.build_phase(phase);

        mfb_cfg = new();
        mfb_cfg.interface_name = {m_config.interface_name, "_mfb"};
        mfb_cfg.active         = m_config.active;
        uvm_config_db #(uvm_mfb::config_item)::set(this, "m_mfb", "m_config", mfb_cfg);
        m_mfb = uvm_mfb::agent_tx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::type_id::create("m_mfb", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        monitor#(REGIONS, REGION_SIZE, BLOCK_SIZE, DIR, META_TYPE, DEVICE) m_monitor_cast;

        super.connect_phase(phase);

        $cast(m_monitor_cast, m_monitor);
        m_mfb.analysis_port.connect(m_monitor_cast.port_mfb);
    endfunction

    task run_phase(uvm_phase phase);
        uvm_mfb::sequence_lib_tx #(REGIONS, REGION_SIZE, BLOCK_SIZE, 32, META_WIDTH) seq_mfb;

        if (get_is_active() == UVM_ACTIVE) begin
            //GENERATE RDY SIGNLA
            seq_mfb = uvm_mfb::sequence_lib_tx #(REGIONS, REGION_SIZE, BLOCK_SIZE, 32, META_WIDTH)::type_id::create("seq_mfb", this);
            seq_mfb.min_random_count = 20;
            seq_mfb.max_random_count = 100;
            seq_mfb.init_sequence();

            fork
                forever begin
                    assert(seq_mfb.randomize()) else `uvm_fatal(this.get_full_name(), "\n\tCannot randomize pcie_mfb sequence");
                    seq_mfb.start(m_mfb.m_sequencer);
                end
            join
        end
    endtask
endclass


class env_mvb_tx #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned BLOCK_SIZE,
    direction_t  DIR,
    device_t DEVICE
) extends env_tx #(REGIONS, REGION_SIZE, BLOCK_SIZE, DIR, MFB_META_NONE, DEVICE);
    `uvm_component_param_utils(uvm_pcie_mfb::env_mvb_tx#(REGIONS, REGION_SIZE, BLOCK_SIZE, DIR, DEVICE));

    // LOCAL PARAMETERS
    localparam MVB_META_WIDTH = meta_width_get(DIR, DEVICE);
    protected uvm_mvb::agent_tx #(REGIONS, MVB_META_WIDTH)                                      m_mvb;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= super.used();
        //ret |= m_avst.used();
        return ret;
    endfunction

    function void build_phase(uvm_phase phase);
        uvm_mvb::config_item mvb_cfg;

        super.build_phase(phase);

        mvb_cfg = new();
        mvb_cfg.interface_name = {m_config.interface_name, "_mvb"};
        mvb_cfg.active         = UVM_PASSIVE;
        uvm_config_db #(uvm_mvb::config_item)::set(this, "m_mvb", "m_config", mvb_cfg);
        m_mvb = uvm_mvb::agent_tx #(REGIONS, MVB_META_WIDTH)::type_id::create("m_mvb", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        monitor#(REGIONS, REGION_SIZE, BLOCK_SIZE, DIR, META_TYPE, DEVICE) m_monitor_cast;

        super.connect_phase(phase);

        $cast(m_monitor_cast, m_monitor);
        m_mvb.analysis_port.connect(m_monitor_cast.port_mvb);
    endfunction
endclass


