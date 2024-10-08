// sequence.sv
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


// Reusable high level sequence. Contains transaction, which has only data part.
class sequence_simple #(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH) extends uvm_sequence #(uvm_header_type::sequence_item#(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH));
    `uvm_object_param_utils(uvm_header_type::sequence_simple#(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH))

    rand int unsigned transaction_count;
    int unsigned transaction_count_min = 100;
    int unsigned transaction_count_max = 200;

    constraint c1 {transaction_count inside {[transaction_count_min : transaction_count_max]};}

    // Constructor - creates new instance of this class
    function new(string name = "sequence_simple");
        super.new(name);
    endfunction

    // Generates transactions
    task body;
        `uvm_info(get_full_name(), "uvm_header_type::sequence_simple is running", UVM_DEBUG)
        repeat(transaction_count)
        begin
            // Generate random request
            `uvm_do_with(req,
            {
                payload_size inside{[2 : PKT_MTU]};
                offset       inside{[0 : payload_size-1]};
                offset       inside{[0 : 2**OFFSET_WIDTH-1]};
                if (LENGTH_WIDTH == $clog2(PKT_MTU)) {
                    length       inside{[0 : payload_size-offset]};
                } else {
                    if (payload_size-offset >= 2**LENGTH_WIDTH-1) {
                        length   inside{[0 : 2**LENGTH_WIDTH-1]};
                    } else {
                        length       inside{[0 : payload_size-offset]};
                    }
                }
            })
            if (req.length+req.offset > req.payload_size) begin
                `uvm_fatal(get_type_name(), $sformatf("LENGTH (%d) + OFFSET (%d) is bigger than PAYLOAD SIZE %d", req.length, req.offset, req.payload_size))
            end
        end
    endtask

endclass

class sequence_one_byte #(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH) extends uvm_sequence #(uvm_header_type::sequence_item#(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH));
    `uvm_object_param_utils(uvm_header_type::sequence_one_byte #(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH))

    rand int unsigned transaction_count;
    int unsigned transaction_count_min = 100;
    int unsigned transaction_count_max = 200;

    constraint c1 {transaction_count inside {[transaction_count_min : transaction_count_max]};}

    // Constructor - creates new instance of this class
    function new(string name = "sequence_two_bytes");
        super.new(name);
    endfunction

    // Generates transactions
    task body;
        `uvm_info(get_full_name(), "uvm_header_type::sequence_two_bytes is running", UVM_DEBUG)
        repeat(transaction_count)
        begin
            // Generate random request
            `uvm_do_with(req,
            {
                payload_size inside{[2 : PKT_MTU]};
                offset       inside{[0 : payload_size-1]};
                offset       inside{[0 : 2**OFFSET_WIDTH-1]};
                length       == 1;
            })
            if (req.length+req.offset > req.payload_size) begin
                `uvm_fatal(get_type_name(), $sformatf("LENGTH (%d) + OFFSET (%d) is bigger than PAYLOAD SIZE %d", req.length, req.offset, req.payload_size))
            end
        end
    endtask

endclass

class sequence_whole_frame_chsum #(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH) extends uvm_sequence #(uvm_header_type::sequence_item#(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH));
    `uvm_object_param_utils(uvm_header_type::sequence_whole_frame_chsum#(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH))

    rand int unsigned transaction_count;
    int unsigned transaction_count_min = 100;
    int unsigned transaction_count_max = 200;

    constraint c1 {transaction_count inside {[transaction_count_min : transaction_count_max]};}

    // Constructor - creates new instance of this class
    function new(string name = "sequence_whole_frame_chsum");
        super.new(name);
    endfunction

    // Generates transactions
    task body;
        `uvm_info(get_full_name(), "uvm_header_type::sequence_whole_frame_chsum is running", UVM_DEBUG)
        repeat(transaction_count)
        begin
            // Generate random request
            `uvm_do_with(req,
            {
                payload_size inside{[1 : PKT_MTU]};
                offset == 0;
                length == payload_size;
            })
            if (req.length+req.offset > req.payload_size) begin
                `uvm_fatal(get_type_name(), $sformatf("LENGTH (%d) + OFFSET (%d) is bigger than PAYLOAD SIZE %d", req.length, req.offset, req.payload_size))
            end
        end
    endtask

endclass

class sequence_zero_offset_rand_length #(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH) extends uvm_sequence #(uvm_header_type::sequence_item#(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH));
    `uvm_object_param_utils(uvm_header_type::sequence_zero_offset_rand_length#(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH))

    rand int unsigned transaction_count;
    int unsigned transaction_count_min = 100;
    int unsigned transaction_count_max = 200;

    constraint c1 {transaction_count inside {[transaction_count_min : transaction_count_max]};}

    // Constructor - creates new instance of this class
    function new(string name = "sequence_zero_offset_rand_length");
        super.new(name);
    endfunction

    // Generates transactions
    task body;
        `uvm_info(get_full_name(), "uvm_header_type::sequence_zero_offset_rand_length is running", UVM_DEBUG)
        repeat(transaction_count)
        begin
            // Generate random request
            `uvm_do_with(req,
            {
                payload_size inside{[1 : PKT_MTU]};
                offset       == 0;
                if (LENGTH_WIDTH == $clog2(PKT_MTU)) {
                    length       inside{[0 : payload_size]};
                } else {
                    if (payload_size >= 2**LENGTH_WIDTH-1) {
                        length   inside{[0 : 2**LENGTH_WIDTH-1]};
                    } else {
                        length       inside{[0 : payload_size]};
                    }
                }
            })
            if (req.length+req.offset > req.payload_size) begin
                `uvm_fatal(get_type_name(), $sformatf("LENGTH (%d) + OFFSET (%d) is bigger than PAYLOAD SIZE %d", req.length, req.offset, req.payload_size))
            end
        end
    endtask

endclass

class sequence_rand_offset_whole_length #(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH) extends uvm_sequence #(uvm_header_type::sequence_item#(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH));
    `uvm_object_param_utils(uvm_header_type::sequence_rand_offset_whole_length#(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH))

    rand int unsigned transaction_count;
    int unsigned transaction_count_min = 100;
    int unsigned transaction_count_max = 200;

    constraint c1 {transaction_count inside {[transaction_count_min : transaction_count_max]};}

    // Constructor - creates new instance of this class
    function new(string name = "sequence_rand_offset_whole_length");
        super.new(name);
    endfunction

    // Generates transactions
    task body;
        `uvm_info(get_full_name(), "uvm_header_type::sequence_rand_offset_whole_length is running", UVM_DEBUG)
        repeat(transaction_count)
        begin
            // Generate random request
            `uvm_do_with(req,
            {
                payload_size inside{[1 : PKT_MTU]};
                offset       inside{[0 : payload_size-1]};
                offset       inside{[0 : 2**OFFSET_WIDTH-1]};
                if (LENGTH_WIDTH == $clog2(PKT_MTU)) {
                    length == payload_size-offset;
                } else {
                    if (payload_size-offset >= 2**LENGTH_WIDTH-1) {
                        length == 2**LENGTH_WIDTH-1 - offset;
                    } else {
                        length == payload_size-offset;
                    }
                }
            })
            if (req.length+req.offset > req.payload_size) begin
                `uvm_fatal(get_type_name(), $sformatf("LENGTH (%d) + OFFSET (%d) is bigger than PAYLOAD SIZE %d", req.length, req.offset, req.payload_size))
            end
        end
    endtask

endclass

/////////////////////////////////////////////////////////////////////////
// SEQUENCE LIBRARY
class sequence_lib #(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH) extends uvm_sequence_library#(sequence_item#(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH));
  `uvm_object_param_utils(uvm_header_type::sequence_lib #(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH))
  `uvm_sequence_library_utils(uvm_header_type::sequence_lib #(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH))

    function new(string name = "sequence_library");
        super.new(name);
        init_sequence_library();
    endfunction

    // subclass can redefine and change run sequences
    // can be useful in specific tests
    virtual function void init_sequence();
        this.add_sequence(uvm_header_type::sequence_simple #(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH)::get_type());
        this.add_sequence(uvm_header_type::sequence_one_byte #(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH)::get_type());
        this.add_sequence(uvm_header_type::sequence_zero_offset_rand_length #(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH)::get_type());
        if (LENGTH_WIDTH == $clog2(PKT_MTU)) begin
            this.add_sequence(uvm_header_type::sequence_whole_frame_chsum #(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH)::get_type());
            this.add_sequence(uvm_header_type::sequence_rand_offset_whole_length #(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH)::get_type());
        end
    endfunction
endclass
