// env.sv: Verification environment
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class env_rx #(
    int unsigned ITEMS,
    direction_t dir,
    string DEVICE,
    logic STRADDLING = 1'b0
) extends uvm_pcie::env_rx;
    `ndk_component_param_utils(
        uvm_pcie_axi::env_rx#(ITEMS, dir, DEVICE, STRADDLING),
        $sformatf("uvm_pcie_axi::env_rx#(%0d,%s,%s,%0d)",ITEMS, dir, DEVICE, STRADDLING)
    );

    // LOCAL PARAMETERS
    localparam ITEM_WIDTH = 32; //as all pcie devices
    localparam TUSER_WIDTH = tuser_width_get(ITEMS, dir);

    //LOW-LEVEL interface
    protected uvm_axi::agent_rx #(ITEMS, ITEM_WIDTH, TUSER_WIDTH) m_axi;
    protected uvm_pcie::bar_config bar = null;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
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
        uvm_axi::config_item axi_cfg;

        assert(DEVICE == "ULTRASCALE") else begin
            `uvm_fatal(this.get_full_name(), "\n\tSUPPORTED ONLY \"ULTRASCALE+\"");
        end
        if (DEVICE == "ULTRASCALE") begin
            `uvm_warning(this.get_full_name(), "\n\tSUPPORTED ONLY \"ULTRASCALE+\"");
        end

        //register driver in factory
        uvm_pcie::monitor::type_id::set_inst_override(monitor_register #(ITEMS, dir, STRADDLING)::get(), "m_monitor", this);
        uvm_pcie::driver::type_id::set_inst_override(driver#(ITEMS, dir)::get_type(), "m_driver", this);

        super.build_phase(phase);

        axi_cfg = new();
        axi_cfg.interface_name = {m_config.interface_name, "_axi"};
        axi_cfg.active         = m_config.active;
        uvm_config_db #(uvm_axi::config_item)::set(this, "m_axi", "m_config", axi_cfg);
        m_axi = uvm_axi::agent_rx #(ITEMS, ITEM_WIDTH, TUSER_WIDTH)::type_id::create("m_axi", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        monitor#(ITEMS, dir) m_monitor_axi;
        driver#(ITEMS, dir)  m_driver_axi;

        super.connect_phase(phase);

        $cast(m_monitor_axi, m_monitor);
        m_axi.analysis_port.connect(m_monitor_axi.port_axi);

        $cast(m_driver_axi, m_driver);
        uvm_config_db#(uvm_common::fifo#(uvm_pcie::header))::set(m_axi.m_sequencer, "" , "in_fifo", m_driver_axi.fifo);
    endfunction

    task run_phase(uvm_phase phase);
        config_sequence seq_cfg;

        uvm_common::sequence_library#(
            config_sequence,
            uvm_axi::sequence_item #(ITEMS, ITEM_WIDTH, tuser_width_get(ITEMS, dir))
        ) seq;

        if (get_is_active() == UVM_ACTIVE) begin
            unique case (dir)
                AXI_RQ: seq = uvm_pcie_axi::sequence_lib_rq#(ITEMS, ITEM_WIDTH)::type_id::create("seq", this);
                AXI_RC: seq = uvm_pcie_axi::sequence_lib_rc#(ITEMS, ITEM_WIDTH, STRADDLING)::type_id::create("seq", this);
                AXI_CQ: seq = uvm_pcie_axi::sequence_lib_cq#(ITEMS, ITEM_WIDTH, STRADDLING)::type_id::create("seq", this);
                AXI_CC: seq = uvm_pcie_axi::sequence_lib_cc#(ITEMS, ITEM_WIDTH)::type_id::create("seq", this);
            endcase

            seq.min_random_count = 20;
            seq.max_random_count = 100;
            seq_cfg = new();
            seq_cfg.bar = bar;
            seq.init_sequence(seq_cfg);

            forever begin
                if(!seq.randomize()) `uvm_fatal(this.get_full_name(), "\n\tCannot randomize pcie_axi sequence");
                seq.start(m_axi.m_sequencer);
            end
        end
    endtask
endclass


class env_tx #(
    int unsigned ITEMS,
    direction_t dir,
    string DEVICE,
    logic STRADDLING = 1'b0
) extends uvm_pcie::env_tx;
    `ndk_component_param_utils(
        uvm_pcie_axi::env_tx#(ITEMS, dir, DEVICE, STRADDLING),
        $sformatf("uvm_pcie_axi::env_tx#(%0d,%s,%s,%0d)",ITEMS, dir, DEVICE, STRADDLING)
    );

    // LOCAL PARAMETERS
    localparam ITEM_WIDTH = 32; //as all pcie devices
    localparam TUSER_WIDTH = tuser_width_get(ITEMS, dir);

    //LOW-LEVEL interface
    protected uvm_axi::agent_tx #(ITEMS, ITEM_WIDTH, TUSER_WIDTH) m_axi;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        uvm_axi::config_item axi_cfg;


        assert(DEVICE == "ULTRASCALE") else begin
            `uvm_fatal(this.get_full_name(), "SUPPORTED ONLY \"ULTRASCALE+\"");
        end
        if (DEVICE == "ULTRASCALE") begin
            `uvm_warning(this.get_full_name(), "SUPPORTED ONLY \"ULTRASCALE+\"");
        end

        //Override monitor
        //uvm_pcie::monitor::type_id::set_inst_override(monitor#(ITEMS, dir, STRADDLING)::get_type(), "m_monitor", this);
        uvm_pcie::monitor::type_id::set_inst_override(monitor_register #(ITEMS, dir, STRADDLING)::get(), "m_monitor", this);

        super.build_phase(phase);

        axi_cfg = new();
        axi_cfg.interface_name = {m_config.interface_name, "_axi"};
        axi_cfg.active         = m_config.active;
        uvm_config_db #(uvm_axi::config_item)::set(this, "m_axi", "m_config", axi_cfg);
        m_axi = uvm_axi::agent_tx #(ITEMS, ITEM_WIDTH, TUSER_WIDTH)::type_id::create("m_axi", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        monitor#(ITEMS, dir) m_monitor_axi;

        super.connect_phase(phase);

        $cast(m_monitor_axi, m_monitor);
        m_axi.analysis_port.connect(m_monitor_axi.port_axi);
    endfunction

    task run_phase(uvm_phase phase);
        uvm_axi::sequence_lib_tx #(ITEMS, ITEM_WIDTH, TUSER_WIDTH) seq;

        if (get_is_active() == UVM_ACTIVE) begin
            // Generate RDY signal
            seq =  uvm_axi::sequence_lib_tx #(ITEMS, ITEM_WIDTH, TUSER_WIDTH)::type_id::create("seq", this);
            seq.min_random_count = 20;
            seq.max_random_count = 100;
            seq.init_sequence();

            forever begin
                if(!seq.randomize()) `uvm_fatal(this.get_full_name(), "\n\tCannot randomize pcie_axi sequence");
                seq.start(m_axi.m_sequencer);
            end
        end
    endtask
endclass

