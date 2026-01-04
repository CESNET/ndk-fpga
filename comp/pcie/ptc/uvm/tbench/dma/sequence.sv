// sequence.sv:
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class sequence_void#(type T_TYPE) extends uvm_sequence #(T_TYPE);
    `uvm_object_param_utils(uvm_dma::sequence_void#(T_TYPE))

    uvm_common::fifo#(T_TYPE) fifo;

    // Constructor - creates new instance of this class
    function new(string name = "sequence_mfb_data");
        super.new(name);
    endfunction

    task body();
        assert(uvm_config_db #(uvm_common::fifo#(T_TYPE))::get(m_sequencer, "", "fifo", fifo)) else begin
            `uvm_fatal(m_sequencer != null ? m_sequencer.get_full_name() : "", "\n\tCannot get fifo");
        end;

        forever begin
            fifo.get(req);
            start_item(req);
            finish_item(req);
        end
    endtask

endclass

