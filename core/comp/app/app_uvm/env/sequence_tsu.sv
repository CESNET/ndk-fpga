/*
 * file       : sequence.sv
 * Copyright (C) 2024 CESNET z. s. p. o.
 * description: verification sequence 
 * date       : 2024
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class sequence_tsu extends uvm_common::sequence_base #(uvm_logic_vector::config_sequence, uvm_logic_vector::sequence_item #(64));

    `uvm_object_utils(uvm_app_core::sequence_tsu);

    rand time time_start;

    // Constructor - creates new instance of this class
    function new(string name = "sequence");
        super.new(name);
    endfunction

    // -----------------------
    // Functions.
    // -----------------------

    // Generates transactions
    task body;
        

        req = uvm_logic_vector::sequence_item #(64)::type_id::create("req", m_sequencer);
        forever begin
            // Generate random request
            start_item(req);
            req.data = (time_start + $time())/1ns;
            finish_item(req); 
        end
    endtask

endclass



