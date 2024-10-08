// driver.sv: pcie driver 
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class driver extends uvm_driver#(uvm_pcie::header);
    `uvm_component_param_utils(uvm_pcie::driver);

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    task run_phase(uvm_phase phase);
    endtask

endclass


