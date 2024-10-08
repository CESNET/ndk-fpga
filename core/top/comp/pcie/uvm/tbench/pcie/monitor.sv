// monitor.sv: pcie monitor 
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class monitor extends uvm_monitor;
    `uvm_component_param_utils(uvm_pcie::monitor);

    uvm_analysis_port #(uvm_pcie::request_header)   cq_analysis_port;
    uvm_analysis_port #(uvm_pcie::completer_header) cc_analysis_port;
    uvm_analysis_port #(uvm_pcie::request_header)   rq_analysis_port;
    uvm_analysis_port #(uvm_pcie::completer_header) rc_analysis_port;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        cq_analysis_port = new("cq_analysis_port", this);
        cc_analysis_port = new("cc_analysis_port", this);
        rq_analysis_port = new("rq_analysis_port", this);
        rc_analysis_port = new("rc_analysis_port", this);
    endfunction

    task run_phase(uvm_phase phase);
    endtask

endclass

