/*
 * file       :  sequence.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: Add config to uvm_sequence
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class sequence_base #(type CONFIG_TYPE, type REQ=uvm_common::sequence_item, type RSP=REQ) extends uvm_sequence#(REQ, RSP);
    `uvm_object_param_utils(uvm_common::sequence_base#(CONFIG_TYPE, REQ, RSP))

    CONFIG_TYPE cfg;

    function new(string name = "sequence_base");
        super.new(name);
    endfunction

    virtual function void config_set(CONFIG_TYPE cfg);
        this.cfg = cfg;
    endfunction

    virtual task pre_start();
        if (this.cfg == null) begin
            this.cfg = new();
        end
    endtask
endclass


