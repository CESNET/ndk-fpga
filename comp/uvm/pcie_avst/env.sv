// env.sv: Verification environment
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class env_rx #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned META_WIDTH,
    int unsigned READY_LATENCY,
    logic STRADDLING
) extends uvm_pcie::env_rx;
    `ndk_component_param_utils(
        uvm_pcie_avst::env_rx#(REGIONS, REGION_SIZE, META_WIDTH, READY_LATENCY, STRADDLING),
                               $sformatf("uvm_pcie_avst::env_rx #(%0d,%0d,%0d,%0d,%0d)", REGIONS, REGION_SIZE,
                                         META_WIDTH, READY_LATENCY, STRADDLING)
    );

    localparam DIRECTION = AVST_DOWN;

    //LOW-LEVEL interface
    protected uvm_avst::agent_rx #(REGIONS, REGION_SIZE, 32, META_WIDTH) m_avst;
    protected uvm_pcie::bar_config bar = null;

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
        bar = cfg;
        //if (get_is_active() == UVM_ACTIVE) begin
        //    //m_sequencer.bar_register(cfg);
        //end
        m_monitor.bar_register(cfg);
    endfunction


    function void build_phase(uvm_phase phase);
        uvm_avst::config_item avst_cfg;

        //register driver in factory
        uvm_pcie::monitor::type_id::set_inst_override(
            monitor #(REGIONS, REGION_SIZE, META_WIDTH, STRADDLING, DIRECTION)::get_type(), "m_monitor", this);
        uvm_pcie::driver::type_id::set_inst_override(driver #(REGIONS, REGION_SIZE, META_WIDTH)::get_type(), "m_driver",
                                                     this);

        super.build_phase(phase);

        avst_cfg = new();
        avst_cfg.interface_name = {m_config.interface_name, "_avst"};
        avst_cfg.active         = m_config.active;
        uvm_config_db #(uvm_avst::config_item)::set(this, "m_avst", "m_config", avst_cfg);
        m_avst = uvm_avst::agent_rx #(REGIONS, REGION_SIZE, 32, META_WIDTH)::type_id::create("m_avst", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        monitor#(REGIONS, REGION_SIZE, META_WIDTH, STRADDLING, DIRECTION) m_monitor_avst;
        driver #(REGIONS, REGION_SIZE, META_WIDTH) m_driver_avst;

        super.connect_phase(phase);

        $cast(m_monitor_avst, m_monitor);
        m_avst.analysis_port.connect(m_monitor_avst.port_avst);

        $cast(m_driver_avst, m_driver);
        // verilog_lint: waive line-length
        uvm_config_db #(uvm_common::fifo #(uvm_pcie::header))::set(m_avst.m_sequencer, "", "in_fifo", m_driver_avst.fifo);
    endfunction

    task run_phase(uvm_phase phase);
        uvm_common::sequence_library#(
            config_sequence,
            uvm_avst::sequence_item #(REGIONS, REGION_SIZE, 32, META_WIDTH)
        ) seq;

        if (get_is_active() == UVM_ACTIVE) begin
            uvm_pcie_avst::config_sequence seq_cfg;
            seq = uvm_pcie_avst::sequence_lib_down#(
                REGIONS,
                REGION_SIZE,
                META_WIDTH,
                READY_LATENCY,
                STRADDLING
            )::type_id::create("seq", this);

            seq.min_random_count = 20;
            seq.max_random_count = 100;
            seq_cfg = new();
            seq_cfg.bar = bar;
            seq.init_sequence(seq_cfg);

            forever begin
                if(!seq.randomize()) begin
                    `uvm_fatal(this.get_full_name(), "\n\tCannot randomize pcie_axi sequence");
                end
                seq.start(m_avst.m_sequencer);
            end
        end
    endtask
endclass


class env_tx #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned META_WIDTH,
    logic STRADDLING
) extends uvm_pcie::env_tx;
    `ndk_component_param_utils(
        uvm_pcie_avst::env_tx#(REGIONS, REGION_SIZE, META_WIDTH, STRADDLING),
        $sformatf("uvm_pcie_avst::env_tx#(%0d,%0d,%0d,%0d)",REGIONS, REGION_SIZE, META_WIDTH, STRADDLING)
    );

    localparam DIRECTION = AVST_UP;

    //LOW-LEVEL interface
    protected uvm_avst::agent_tx #(REGIONS, REGION_SIZE, 32, META_WIDTH) m_avst;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        //ret |= super.used();
        //ret |= m_avst.used();
        return ret;
    endfunction

    function void build_phase(uvm_phase phase);
        uvm_avst::config_item avst_cfg;


        //Override monitor
        //uvm_pcie::monitor::type_id::set_inst_override(monitor#(ITEMS, dir, STRADDLING)::get_type(), "m_monitor", this);
        uvm_pcie::monitor::type_id::set_inst_override(
            monitor #(REGIONS, REGION_SIZE, META_WIDTH, STRADDLING, DIRECTION)::get_type(), "m_monitor", this);

        super.build_phase(phase);

        avst_cfg = new();
        avst_cfg.interface_name = {m_config.interface_name, "_avst"};
        avst_cfg.active         = m_config.active;
        uvm_config_db #(uvm_avst::config_item)::set(this, "m_avst", "m_config", avst_cfg);
        m_avst = uvm_avst::agent_tx #(REGIONS, REGION_SIZE, 32, META_WIDTH)::type_id::create("m_avst", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        monitor#(REGIONS, REGION_SIZE, META_WIDTH, STRADDLING, DIRECTION) m_monitor_avst;

        super.connect_phase(phase);

        $cast(m_monitor_avst, m_monitor);
        m_avst.analysis_port.connect(m_monitor_avst.port_avst);
    endfunction

    task run_phase(uvm_phase phase);
        uvm_avst::sequence_lib_tx #(REGIONS, REGION_SIZE, 32, META_WIDTH) seq;

        if (get_is_active() == UVM_ACTIVE) begin
            // Generate RDY signal
            seq =  uvm_avst::sequence_lib_tx #(REGIONS, REGION_SIZE, 32, META_WIDTH)::type_id::create("seq", this);
            seq.min_random_count = 20;
            seq.max_random_count = 100;
            seq.init_sequence();

            forever begin
                if(!seq.randomize()) begin
                    `uvm_fatal(this.get_full_name(), "\n\tCannot randomize pcie_axi sequence");
                end
                seq.start(m_avst.m_sequencer);
            end
        end
    endtask
endclass

