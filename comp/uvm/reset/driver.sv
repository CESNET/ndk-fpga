/*
 * file       : driver.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: driver drives RESET sequence item if there is no then keep previous value.
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/



class driver extends uvm_driver#(sequence_item);
    `uvm_component_utils(uvm_reset::driver);

    sync  cbs[$];
    logic   reset_prev = 1'b0;
    logic   reset = 1'b0;
    virtual reset_if.driver vif;

    //consturcton
    function new (string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void sync_connect(sync s);
       cbs.push_back(s);
    endfunction

    function void send_reset();
        time time_act = $time();
        foreach (cbs[it]) begin
            if (reset) begin
                cbs[it].reset_start(time_act);
            end else begin
                cbs[it].reset_stop(time_act);
            end
        end
    endfunction

    task run_phase(uvm_phase phase);
        //init reset
        vif.driver_cb.RESET <= 1'b0;

        forever begin
            seq_item_port.try_next_item(req);
            if (req != null) begin
                reset  = req.reset;
                seq_item_port.item_done();
            end

            if (reset_prev != reset) begin
                send_reset();
            end
            reset_prev = reset;

            vif.driver_cb.RESET <= reset;
            @(vif.driver_cb);
        end
    endtask
endclass
