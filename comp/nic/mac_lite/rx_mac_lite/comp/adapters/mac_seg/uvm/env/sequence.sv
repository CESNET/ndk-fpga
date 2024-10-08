/*
 * file       : sequence.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: sequence simple
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class seq_small_pkt extends uvm_logic_vector_array::sequence_simple#(8);
    `uvm_object_utils(uvm_mac_seg_rx::seq_small_pkt)
    function new(string name="seq_small_pkt");
        super.new(name);
        cfg = new();
        cfg.array_size_set(12, 128);

        //cfg.transaction_count_set(1, 20);
        transaction_count_min = 1;
        transaction_count_max = 20;
    endfunction

    function void config_set(uvm_logic_vector_array::config_sequence cfg);
    endfunction
endclass


class sequence_error#(LOGIC_WIDTH) extends uvm_logic_vector::sequence_simple#(LOGIC_WIDTH);
    `uvm_object_param_utils(uvm_mac_seg_rx::sequence_error#(LOGIC_WIDTH))

	function new (string name = "");
		super.new(name);
	endfunction

    task body;
        repeat(transaction_count)
        begin
            // Generate random request
            `uvm_do_with(req, { data dist {0 :/ 10, [0:2**LOGIC_WIDTH-1] :/ 1};})
        end
    endtask
endclass

class sequence_simple_1 extends uvm_sequence;
    `uvm_object_utils(uvm_mac_seg_rx::sequence_simple_1)
    `uvm_declare_p_sequencer(uvm_mac_seg_rx::sequencer);

    localparam LOGIC_WIDTH = 6;

    //////////////////////////////////
    // variables
    uvm_sequence #(uvm_logic_vector_array::sequence_item#(8))   rx_packet;
    uvm_logic_vector::sequence_simple#(LOGIC_WIDTH) rx_error;
    uvm_sequence#(uvm_reset::sequence_item)         reset_seq;

    //////////////////////////////////
    // functions
    function new (string name = "");
        super.new(name);
    endfunction

    virtual function void seq_create();
              uvm_logic_vector_array::sequence_lib#(8) rx_packet_lib;

        rx_packet_lib = uvm_logic_vector_array::sequence_lib#(8)::type_id::create("seq_data");
        rx_packet_lib.init_sequence();
        rx_packet_lib.add_sequence(seq_small_pkt::get_type());
        rx_packet_lib.min_random_count = 100;
        rx_packet_lib.max_random_count = 200;

        rx_error  = sequence_error#(LOGIC_WIDTH)::type_id::create("avalon_rx_seq_base");
        reset_seq = uvm_reset::sequence_start::type_id::create("reset_simple");

		rx_packet = rx_packet_lib;
	endfunction

    task error_rx();
        forever begin
            rx_error.randomize();
            rx_error.start(p_sequencer.rx_error);
        end

    endtask

    task reset();
        forever  begin
            reset_seq.randomize();
            reset_seq.start(p_sequencer.reset);
        end
    endtask

    //////////////////////////////
    //run all sequences paralelly
    task body;
        fork
            reset();
            error_rx();
        join_none

        assert(rx_packet.randomize());
        rx_packet.start(p_sequencer.rx_packet);
    endtask
endclass
