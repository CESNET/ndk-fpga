//-- sequence.sv
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// This low level sequence define bus functionality
class logic_vector_array_sequence extends uvm_sequence #(uvm_logic_vector_array::sequence_item #(32));
    `uvm_object_utils(uvm_dma_up::logic_vector_array_sequence)

    mailbox#(uvm_logic_vector_array::sequence_item #(32)) tr_export;

    function new(string name = "sequence_simple_lva_rx");
        super.new(name);
    endfunction

    task body;
        forever begin
            tr_export.get(req);
            start_item(req);
            finish_item(req);
        end
    endtask
endclass

class logic_vector_sequence#(META_WIDTH) extends uvm_sequence #(uvm_logic_vector::sequence_item#(META_WIDTH));
    `uvm_object_param_utils(uvm_dma_up::logic_vector_sequence#(META_WIDTH))

    mailbox#(uvm_logic_vector::sequence_item#(META_WIDTH)) tr_export;

    function new(string name = "sequence_simple_lv_rx");
        super.new(name);
    endfunction

    task body;
        forever begin
            tr_export.get(req);
            start_item(req);
            finish_item(req);
        end
    endtask
endclass
