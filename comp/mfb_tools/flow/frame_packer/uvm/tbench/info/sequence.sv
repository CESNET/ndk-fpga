// sequence.sv
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): David Beneš <xbenes52@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


// Reusable high level sequence. Contains transaction, which has only data part.
class sequence_simple#(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH) extends uvm_sequence #(sequence_item #(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH));
    `uvm_object_param_utils(uvm_meta::sequence_simple#(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH))

    rand int unsigned transaction_count;
    int unsigned transaction_count_min = 10;
    int unsigned transaction_count_max = 100;
    uvm_common::rand_length   rdy_length;

    constraint c1 {transaction_count inside {[transaction_count_min : transaction_count_max]};}

    // Constructor - creates new instance of this class
    function new(string name = "sequence");
        super.new(name);
        rdy_length = uvm_common::rand_length_rand::new();
    endfunction

    // Generates transactions
    task body;
        `uvm_info(get_full_name(), "uvm_meta::sequence_simple is running", UVM_DEBUG)
        repeat(transaction_count)
        begin
            int unsigned channel_next;

            void'(rdy_length.randomize());
            channel_next = rdy_length.m_value % RX_CHANNELS;
            // Generate random request, which must be in interval from min length to max length
            `uvm_do_with(req, {channel == channel_next; });
        end
    endtask
endclass

class sequence_simple_rand#(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH) extends uvm_sequence #(sequence_item #(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH));
    `uvm_object_param_utils(uvm_meta::sequence_simple_rand#(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH))

    rand int unsigned transaction_count;
    int unsigned transaction_count_min = 10;
    int unsigned transaction_count_max = 100;
    rand int unsigned channel_max; // 2048
    rand int unsigned channel_min;

    constraint c1 {transaction_count inside {[transaction_count_min : transaction_count_max]};}
    constraint channel_num_c {channel_min inside {[0 : RX_CHANNELS]}; channel_max inside {[0 : RX_CHANNELS]}; channel_min <= channel_max;}

    // Constructor - creates new instance of this class
    function new(string name = "sequence");
        super.new(name);
    endfunction

    // Generates transactions
    task body;
        `uvm_info(get_full_name(), "uvm_meta::sequence_simple_rand is running", UVM_DEBUG)
        repeat(transaction_count)
        begin
            // Generate random request, which must be in interval from min length to max length
            `uvm_do_with(req, {channel inside{[channel_min : channel_max]}; });
        end
    endtask
endclass

class sequence_simple_rand_dist#(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH) extends uvm_sequence #(sequence_item #(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH));
    `uvm_object_param_utils(uvm_meta::sequence_simple_rand_dist#(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH))

    rand int unsigned transaction_count;
    int unsigned transaction_count_min = 10;
    int unsigned transaction_count_max = 200;
    int unsigned channel_min = 0;
    int unsigned channel_max = RX_CHANNELS; // 2048

    constraint c1 {transaction_count inside {[transaction_count_min : transaction_count_max]};}

    // Constructor - creates new instance of this class
    function new(string name = "sequence");
        super.new(name);
    endfunction

    // Generates transactions
    task body;
        `uvm_info(get_full_name(), "uvm_meta::sequence_simple_rand_dist is running", UVM_DEBUG)
        repeat(transaction_count)
        begin
            // Generate random request, which must be in interval from min length to max length
            `uvm_do_with(req, {channel inside{[channel_min : channel_max]}; });
        end
    endtask
endclass

class sequence_simple_channel#(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH) extends uvm_sequence #(sequence_item #(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH));
    `uvm_object_param_utils(uvm_meta::sequence_simple_channel#(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH))

    rand int unsigned transaction_count;
    int unsigned transaction_count_min = 10;
    int unsigned transaction_count_max = 20;
    rand int unsigned channel;

    constraint c1 {transaction_count inside {[transaction_count_min : transaction_count_max]};}
    constraint channel_num_c {channel inside {[0 : RX_CHANNELS]};}

    // Constructor - creates new instance of this class
    function new(string name = "sequence");
        super.new(name);
    endfunction

    // Generates transactions
    task body;
        `uvm_info(get_full_name(), "uvm_meta::sequence_simple_channel is running", UVM_DEBUG)
        repeat(transaction_count)
        begin
            // Generate random request, which must be in interval from min length to max length
            `uvm_do_with(req, {channel == this.channel;});
        end
    endtask
endclass


//////////////////////////////////////
// TX LIBRARY
class sequence_lib#(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH) extends uvm_sequence_library#(sequence_item #(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH));
  `uvm_object_param_utils(uvm_meta::sequence_lib#(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH))
  `uvm_sequence_library_utils(uvm_meta::sequence_lib#(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH))

    function new(string name = "");
        super.new(name);
        init_sequence_library();
    endfunction

    // subclass can redefine and change run sequences
    // can be useful in specific tests
    virtual function void init_sequence();
        //this.add_sequence(sequence_simple#(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH)::get_type());
        //this.add_sequence(sequence_simple_rand#(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH)::get_type());
        //this.add_sequence(sequence_simple_rand_dist#(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH)::get_type());
        this.add_sequence(sequence_simple_channel#(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH)::get_type());
    endfunction
endclass
