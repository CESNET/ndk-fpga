// env.sv: Environment for Intel R-Tile device
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class env_rx #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned META_WIDTH,
    int unsigned READY_LATENCY,
    logic STRADDLING
) extends uvm_pcie_avst::env_rx#(REGIONS, REGION_SIZE, META_WIDTH, READY_LATENCY, STRADDLING);
    `uvm_component_param_utils(
        uvm_pcie_intel_r_tile::env_rx #(REGIONS, REGION_SIZE, META_WIDTH, READY_LATENCY, STRADDLING));

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        //register driver in factory
        //uvm_pcie::monitor::type_id::set_inst_override(uvm_pcie_avst::monitor #(REGIONS, REGION_SIZE, META_WIDTH, DIRECTION)::get_type(), "m_monitor", this);
        // FIRST REGISTRATION of OVERRIDE WIN.
        uvm_pcie::driver::type_id::set_inst_override(driver #(REGIONS, REGION_SIZE, META_WIDTH)::get_type(), "m_driver",
                                                     this);

        //uvm_pcie::env_rx::build_phase(phase);
        super.build_phase(phase);
    endfunction
endclass


class env_tx #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned META_WIDTH,
    logic STRADDLING
) extends uvm_pcie_avst::env_tx#(REGIONS, REGION_SIZE, META_WIDTH, STRADDLING);
    `uvm_component_param_utils(uvm_pcie_intel_r_tile::env_tx#(REGIONS, REGION_SIZE, META_WIDTH, STRADDLING));

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    task run_phase(uvm_phase phase);
        // avst cannot generate rdy signal set to zero
        //uvm_avst::sequence_lib_tx #(REGIONS, REGION_SIZE, 32, META_WIDTH)::type_id::set_inst_override(
        //    uvm_avst::sequence_lib_tx_speed#(REGIONS, REGION_SIZE, 32, META_WIDTH)::get_type(),
        //    "seq", this
        //);
        super.run_phase(phase);
    endtask
endclass


