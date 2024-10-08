// sequence.sv: 
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class req_fifo#(type T_ITEM);
    protected T_ITEM items[$];

    function int unsigned size();
        return items.size();
    endfunction

    function void push_back(T_ITEM item);
        items.push_back(item);
    endfunction

    function T_ITEM pop_front();
        return items.pop_front();
    endfunction
endclass


class sequence_void#(type T_TYPE) extends uvm_sequence #(T_TYPE);
    `uvm_object_param_utils(uvm_dma::sequence_void#(T_TYPE))

    req_fifo#(T_TYPE) fifo; 

    // Constructor - creates new instance of this class
    function new(string name = "sequence_mfb_data");
        super.new(name);
    endfunction

    task body();
        assert(uvm_config_db #(req_fifo#(T_TYPE))::get(m_sequencer, "", "fifo", fifo)) else begin
            `uvm_fatal(m_sequencer != null ? m_sequencer.get_full_name() : "", "\n\tCannot get fifo"); 
        end;

        forever begin
            wait(fifo.size() != 0);
            req = fifo.pop_front();
            start_item(req);
            finish_item(req);
        end
    endtask

endclass



