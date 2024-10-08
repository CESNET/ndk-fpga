/*
 * file       : sequencer.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: MI sequencer
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class sequencer_slave #(int unsigned DATA_WIDTH, int unsigned ADDR_WIDTH, int unsigned META_WIDTH = 0) extends uvm_sequencer #(sequence_item_request #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH), sequence_item_response #(DATA_WIDTH));
    `uvm_component_param_utils(uvm_mi::sequencer_slave #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH))

    function new(string name = "sequencer", uvm_component parent);
        super.new(name, parent);
    endfunction: new
endclass


class sequencer_master #(int unsigned DATA_WIDTH, int unsigned ADDR_WIDTH, int unsigned META_WIDTH = 0) extends uvm_sequencer #(sequence_item_response #(DATA_WIDTH), sequence_item_request #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH));
    `uvm_component_param_utils(uvm_mi::sequencer_master #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH))

    sequence_item_request#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) tr_rd[$];
    uvm_reset::sync_terminate sync;

    function new(string name = "sequencer", uvm_component parent);
        super.new(name, parent);
        tr_rd.delete();
    endfunction: new

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        sync = new();
    endfunction
endclass



