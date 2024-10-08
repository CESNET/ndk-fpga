// monitor.sv: LBUS monitor
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class monitor extends uvm_monitor;
    `uvm_component_utils(uvm_lbus::monitor)

    // Virtual interface
    virtual lbus_if.monitor vif;

    // Analysis port
    uvm_analysis_port #(sequence_item) analysis_port;

    // Constructor
    function new(string name = "monitor", uvm_component parent = null);
        super.new(name, parent);

        analysis_port = new("analysis_port", this);
    endfunction

    task run_phase(uvm_phase phase);
        sequence_item item;

        forever begin
            @(vif.monitor_cb);

            item = sequence_item::type_id::create("item");
            // Sampling
            item.data = vif.monitor_cb.DATA;
            item.ena  = vif.monitor_cb.ENA;
            item.sop  = vif.monitor_cb.SOP;
            item.eop  = vif.monitor_cb.EOP;
            item.err  = vif.monitor_cb.ERR;
            item.mty  = vif.monitor_cb.MTY;
            item.rdy  = vif.monitor_cb.RDY;
            // Write sequence item to analysis port
            analysis_port.write(item);
        end
    endtask

endclass
