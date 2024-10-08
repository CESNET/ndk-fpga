/*
 * file       : sequence_not_rdy_once_for_32_ticks_tx.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: LII sequence
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

//PCS

// Sequence which set rdy once per 32 ticks
class sequence_not_rdy_once_for_32_ticks_tx #(int unsigned DATA_WIDTH, int unsigned META_WIDTH, int unsigned SOF_WIDTH) extends uvm_sequence #(uvm_lii::sequence_item #(DATA_WIDTH, META_WIDTH, SOF_WIDTH));

    // ------------------------------------------------------------------------
    // Registration of agent to databaze
    `uvm_object_param_utils(uvm_byte_array_lii::sequence_not_rdy_once_for_32_ticks_tx #(DATA_WIDTH, META_WIDTH, SOF_WIDTH))

    // ------------------------------------------------------------------------
    // Variables
    uvm_common::rand_rdy rdy;
    // ------------------------------------------------------------------------
    // Constructor
    function new(string name = "sequence_not_rdy_once_for_32_ticks_tx");
        super.new(name);
        rdy = uvm_common::rand_rdy_swap::new(32, 1);
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
