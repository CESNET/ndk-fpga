//-- my_sequence.sv: Custom sequence
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class single_transaction_sequence #(DATA_WIDTH) extends uvm_sequence #(uvm_logic_vector::sequence_item #(DATA_WIDTH));
    `uvm_object_param_utils(single_transaction_sequence #(DATA_WIDTH))

    // Constructor - creates new instance of this class
    function new(string name = "single_transaction_sequence");
        super.new(name);
    endfunction

    // -----------------------
    // Functions.
    // -----------------------

    // Generates transactions
    task body;
        // Generate random request
        `uvm_do(req)
    endtask

endclass
