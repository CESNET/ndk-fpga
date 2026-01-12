// driver.sv: pcie driver
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class driver#(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned META_WIDTH
) extends uvm_pcie::driver;
    `uvm_component_param_utils(uvm_pcie_avst::driver #(REGIONS, REGION_SIZE, META_WIDTH));

    uvm_common::fifo#(uvm_pcie::header) fifo;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        fifo = new("fifo", this);
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= super.used();
        ret |= fifo.used();
        return ret;
    endfunction

    task run_phase(uvm_phase phase);
        forever begin
            // TODO: THING ABOUT IT
            wait(fifo.size() < REGIONS);
            seq_item_port.get_next_item(req);
            fifo.push_back(req);
            seq_item_port.item_done();
        end
    endtask

endclass


