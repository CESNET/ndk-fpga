//-- sequence.sv
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


// Reusable high level sequence. Contains transaction, which has only data part.
class sequence_simple #(DEVICE) extends uvm_sequence #(uvm_ptc_info_rc::sequence_item);
    `uvm_object_utils(uvm_ptc_info_rc::sequence_simple #(DEVICE))

    rand int unsigned transaction_count;
    int unsigned transaction_count_min = 100;
    int unsigned transaction_count_max = 100;

    constraint c1 {transaction_count inside {[transaction_count_min : transaction_count_max]};}

    // Constructor - creates new instance of this class
    function new(string name = "sequence");
        super.new(name);
    endfunction

    // Generates transactions
    task body;
        `uvm_info(get_full_name(), "uvm_ptc_info_rc::sequence_simple is running", UVM_DEBUG)
        repeat(transaction_count)
        begin
            // Generate random request, which must be in interval from min length to max length
            `uvm_do(req);
        end
    endtask

endclass


