// monitor.sv: pcie monitor
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class monitor extends uvm_monitor;
    `ndk_component_utils(uvm_pcie::monitor);

    uvm_analysis_port #(uvm_pcie::header)   analysis_port;
    uvm_reset::sync_terminate reset_sync;

    protected bar_config bar_cfg;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        analysis_port = new("cq_analysis_port", this);
        reset_sync = new();
    endfunction

    function void bar_register(bar_config cfg);
        bar_cfg = cfg;
    endfunction
endclass

