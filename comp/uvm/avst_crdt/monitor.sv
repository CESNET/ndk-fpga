// monitor.sv: AVST credit control monitor
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class monitor #(int unsigned UPDATE_CNT_WIDTH) extends uvm_monitor;
    `uvm_component_param_utils(uvm_avst_crdt::monitor #(UPDATE_CNT_WIDTH))

    // Virtual interface
    virtual avst_crdt_if #(UPDATE_CNT_WIDTH).monitor vif;

    // Analysis port
    uvm_analysis_port #(sequence_item #(UPDATE_CNT_WIDTH)) analysis_port;

    // Constructor
    function new(string name = "monitor", uvm_component parent = null);
        super.new(name, parent);

        analysis_port = new("analysis_port", this);
    endfunction

    task run_phase(uvm_phase phase);
        sequence_item #(UPDATE_CNT_WIDTH) item;

        forever begin
            @(vif.monitor_cb);

            item = sequence_item #(UPDATE_CNT_WIDTH)::type_id::create("item");
            // Sampling
            item.init       = vif.monitor_cb.INIT;
            item.init_ack   = vif.monitor_cb.INIT_ACK;
            item.update     = vif.monitor_cb.UPDATE;
            item.update_cnt = vif.monitor_cb.UPDATE_CNT;
            // Write sequence item to analysis port
            item.start[this.get_full_name()] = $time();
            analysis_port.write(item);
        end
    endtask

endclass
