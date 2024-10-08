/*
 * file       : monitor.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: RESET monitor
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


class monitor extends uvm_monitor;
    `uvm_component_utils(uvm_reset::monitor);

    virtual reset_if.monitor vif;

    logic reset_prev;
    sync  cbs[$];
    uvm_analysis_port #(sequence_item) analysis_port;
    sequence_item item;

    function new (string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void sync_connect(sync s);
       cbs.push_back(s);
    endfunction

    function void send_reset(logic reset);
        time time_act = $time();
        foreach (cbs[it]) begin
            if (reset === 1) begin
                cbs[it].reset_start(time_act);
            end else if (reset === 0) begin
                cbs[it].reset_stop(time_act);
            end
        end
    endfunction

    function void build_phase(uvm_phase phase);
        analysis_port = new("anaylsis port", this);
        item = sequence_item::type_id::create("item");
    endfunction

    task run_phase(uvm_phase phase);
        logic reset_new;

        reset_prev = 1'b0;
        forever begin
            @(vif.monitor_cb);
            reset_new  = vif.monitor_cb.RESET;

            if (reset_new !== reset_prev) begin
                send_reset(reset_new);
            end
            item = sequence_item::type_id::create("item");
            item.reset = reset_new;
            analysis_port.write(item);

            reset_prev = reset_new;
        end
    endtask
endclass
