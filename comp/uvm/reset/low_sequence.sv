/*
 * file       : low_sequence.sv
 * description:  sequence check driver variable if reset is set
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: RESET packages
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class low_sequence extends uvm_sequence#(uvm_reset::sequence_item);
    `uvm_object_utils(uvm_reset::low_sequence)

    env_driver driver;

    function new (string name = "sequence_reset");
        super.new(name);
    endfunction

    task body;
        req = sequence_item::type_id::create("req");

        forever begin
            start_item(req);
            req.reset = driver.signal_reset;
            finish_item(req);
        end
    endtask
endclass


