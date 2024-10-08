/*
 * file       : sequence_simple_tx_random_rdy.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: LII sequence
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

//MAC

// Sequence which generate random rdy
class sequence_simple_tx_random_rdy #(int unsigned DATA_WIDTH, int unsigned META_WIDTH, int unsigned SOF_WIDTH) extends uvm_sequence #(uvm_lii::sequence_item #(DATA_WIDTH, META_WIDTH, SOF_WIDTH));

    // ------------------------------------------------------------------------
    // Registration of agent to databaze
    `uvm_object_param_utils(uvm_byte_array_lii::sequence_simple_tx_random_rdy #(DATA_WIDTH, META_WIDTH, SOF_WIDTH))
    uvm_common::rand_rdy                 rdy;

    // ------------------------------------------------------------------------
    // Constructor
    function new(string name = "sequence_simple_tx_random_rdy");
        super.new(name);
        rdy = uvm_common::rand_rdy_rand::new();
    endfunction

    // ------------------------------------------------------------------------
    // Generates transactions
    task body;
        // Create a request for sequence item
        req = uvm_lii::sequence_item #(DATA_WIDTH, META_WIDTH, SOF_WIDTH)::type_id::create("req");
        forever begin
            start_item(req);
            if(!req.randomize()) `uvm_fatal(this.get_full_name(), "failed to radnomize");
            void'(rdy.randomize());
            req.rdy = rdy.m_value;
            finish_item(req);
        end
    endtask

endclass
