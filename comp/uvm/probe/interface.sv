/*
 * file       : inf.sv
 * Copyright (C) 2023 CESNET z. s. p. o.
 * description: probe interface
 * date       : 2023
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

interface probe_inf #(int unsigned DATA_WIDTH) (
    input wire logic event_signal,
    input wire logic [DATA_WIDTH-1:0] event_data,
    input wire logic CLK);

    import uvm_pkg::*;
    localparam string PATH = $psprintf("%m");

    class probe_event_component;
        uvm_event probe_event;

        function new();
            uvm_probe::pool pool;

            pool = uvm_probe::pool::get_global_pool();
            probe_event = new();
            pool.add({"probe_event_component_", PATH}, probe_event);
        endfunction

        task body();
            uvm_probe::data#(DATA_WIDTH) data = uvm_probe::data#(DATA_WIDTH)::type_id::create({"probe_event_component", PATH}, null);
            forever begin
                @(posedge CLK);
                if (event_signal == 1'b1) begin
                    data.data = event_data;
                    probe_event.trigger(data);
                end
            end
        endtask
    endclass

    probe_event_component env;

    initial begin
        env = new();
        env.body();
    end
endinterface
