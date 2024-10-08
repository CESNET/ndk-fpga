/*
 * file       : env_driver.sv
 * description: driver generate reset signal for lower level sequences
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: RESET packages
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class env_driver extends uvm_driver#(sequence_item);
    `uvm_component_utils(uvm_reset::env_driver);

    int unsigned signal_reset = 1'b0;
    time         delay = 20ns;

    function new (string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    task run_phase(uvm_phase phase);

        //init reset
        forever begin
            seq_item_port.try_next_item(req);
            if (req != null) begin
                signal_reset = req.reset;
            end
            #(delay);

            if (req != null) begin
                seq_item_port.item_done();
            end
        end
    endtask


endclass

