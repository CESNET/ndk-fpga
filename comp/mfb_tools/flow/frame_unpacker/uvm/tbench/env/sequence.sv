// sequence.sv Sequence generating superpackets
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

// This low level sequence define bus functionality
class logic_vector_array_sequence #(MFB_ITEM_WIDTH) extends uvm_sequence#(uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH));
    `uvm_object_param_utils(uvm_superunpacketer::logic_vector_array_sequence #(MFB_ITEM_WIDTH))

    mailbox#(uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH)) tr_export;

    function new(string name = "superpacket_sequence");
        super.new(name);
    endfunction

    task body;
        forever begin
            wait(tr_export.num() > 0);
            tr_export.get(req);
            start_item(req);
            finish_item(req);
        end
    endtask
endclass

class mvb_data_sequence #(MVB_ITEM_WIDTH) extends uvm_sequence#(uvm_logic_vector::sequence_item #(MVB_ITEM_WIDTH));
    `uvm_object_param_utils(uvm_superunpacketer::mvb_data_sequence #(MVB_ITEM_WIDTH))

    mailbox#(uvm_logic_vector::sequence_item #(MVB_ITEM_WIDTH)) tr_export;

    function new(string name = "superpacket_sequence");
        super.new(name);
    endfunction

    task body;
        forever begin
            wait(tr_export.num() > 0);
            tr_export.get(req);
            start_item(req);
            finish_item(req);
        end
    endtask
endclass
