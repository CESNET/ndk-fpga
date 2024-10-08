// sequence_set.sv Sequence generating user defined MI and data transactions
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): David Beneš <xbenes52@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class sequence_mfb_data #(DATA_WIDTH) extends uvm_sequence #(uvm_logic_vector_array::sequence_item #(DATA_WIDTH));
    `uvm_object_param_utils(uvm_framepacker::sequence_mfb_data#(DATA_WIDTH))

    mailbox#(uvm_logic_vector_array::sequence_item #(DATA_WIDTH)) tr_export;

    // Constructor - creates new instance of this class
    function new(string name = "sequence_mfb_data");
        super.new(name);
    endfunction

    // -----------------------
    // Functions.
    // -----------------------

    // Generates transactions
    task body;
        forever begin
            tr_export.get(req);
            start_item(req);
            finish_item(req);
        end
    endtask


endclass

class sequence_mvb_data #(MVB_ITEM_WIDTH) extends uvm_sequence #(uvm_logic_vector::sequence_item #(MVB_ITEM_WIDTH));

    `uvm_object_param_utils(uvm_framepacker::sequence_mvb_data#(MVB_ITEM_WIDTH))

    mailbox#(uvm_logic_vector::sequence_item #(MVB_ITEM_WIDTH)) tr_export;

    // Constructor - creates new instance of this class
    function new(string name = "sequence_mvb_data");
        super.new(name);
    endfunction

    // -----------------------
    // Functions.
    // -----------------------

    // Generates transactions
    task body;
        forever begin
            tr_export.get(req);
            start_item(req);
            finish_item(req);
        end
    endtask


endclass
