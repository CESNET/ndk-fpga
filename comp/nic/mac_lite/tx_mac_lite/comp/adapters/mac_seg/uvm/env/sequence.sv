/*
 * file       : sequence.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: sequence simple
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class sequence_meta extends uvm_sequence #(uvm_logic_vector::sequence_item #(1));
    `uvm_object_utils(uvm_mac_seg_tx::sequence_meta)

    function new(string name = "sequence_meta");
        super.new(name);
    endfunction

    // Generates transactions
    task body;
        forever begin
            // Generate random request
            `uvm_do_with(req, {data dist {0 := 10, 1 := 1};})
        end
    endtask

endclass


class sequence_simple_1#(SEGMENTS) extends uvm_sequence;
    `uvm_object_param_utils(uvm_mac_seg_tx::sequence_simple_1#(SEGMENTS))
    `uvm_declare_p_sequencer(uvm_mac_seg_tx::sequencer#(SEGMENTS));

    localparam ITEM_WIDTH = 8;

	//byte_array::sequence_simple rx_seq;
	uvm_sequence#(uvm_reset::sequence_item)          reset_seq;
    uvm_sequence #(uvm_logic_vector::sequence_item #(1)) rx_seq_meta;
    uvm_sequence #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH))        rx_seq_data;
    uvm_intel_mac_seg::sequence_simple_tx#(SEGMENTS) tx_seq;

    //////////////////////////////////
    // functions
    function new (string name = "");
        super.new(name);
    endfunction

    virtual function void seq_create();
        uvm_logic_vector_array::sequence_lib#(ITEM_WIDTH) rx_seq_data_lib;

        rx_seq_meta = sequence_meta::type_id::create("seq_meta");
        rx_seq_data_lib = uvm_logic_vector_array::sequence_lib#(ITEM_WIDTH)::type_id::create("seq_data");
        rx_seq_data_lib.init_sequence();
        rx_seq_data_lib.min_random_count = 50;
        rx_seq_data_lib.max_random_count = 100;
        rx_seq_data_lib.cfg = new();

        reset_seq   = uvm_reset::sequence_start::type_id::create("reset_simple");
        tx_seq      = uvm_intel_mac_seg::sequence_simple_tx#(SEGMENTS)::type_id::create("intel_mac_tx_seq");

        rx_seq_data = rx_seq_data_lib;
        //rx_seq_data = uvm_logic_vector_array::sequence_simple#(ITEM_WIDTH)::type_id::create("seq_data");
    endfunction

	task intel_mac_seg_tx();
        forever begin
	        tx_seq.randomize();
            tx_seq.start(p_sequencer.tx_sequencer);
        end
	endtask

	task meta_rx();
        forever begin
			rx_seq_meta.randomize();
            rx_seq_meta.start(p_sequencer.rx_sequencer.m_meta);
        end
	endtask

	task reset();
        forever  begin
	        reset_seq.randomize();
            reset_seq.start(p_sequencer.reset_sequencer);
        end
	endtask

    //////////////////////////////
    //run all sequences paralelly
    task body;
		fork
			reset();
			intel_mac_seg_tx();
			meta_rx();
		join_none

        for (int unsigned it = 0; it < 5; it++) begin
            rx_seq_data.randomize();
            rx_seq_data.start(p_sequencer.rx_sequencer.m_data);
        end
    endtask
endclass

