/*
 * file       : sequence.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: byte array sequence
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


// Reusable high level sequence. Contains transaction, which has only data part.
class sequence_simple extends uvm_common::sequence_base#(config_sequence, sequence_item);
    `uvm_object_utils(uvm_byte_array::sequence_simple)
    `uvm_declare_p_sequencer(uvm_byte_array::sequencer);

    rand int unsigned transaction_count;

    constraint c1 {transaction_count inside {[cfg.transaction_count_min : cfg.transaction_count_max]};}

    // Constructor - creates new instance of this class
    function new(string name = "sequence_simple");
        super.new(name);
    endfunction

    // -----------------------
    // Functions.
    // -----------------------
    task body;
        `uvm_info(get_full_name(), "sequence_simple is running", UVM_DEBUG)

        repeat(transaction_count)
        begin
            // Generate random request, which must be in interval from min length to max length
            `uvm_do_with(req, {data.size inside{[cfg.array_size_min : cfg.array_size_max]}; });
        end
    endtask

endclass

// High level sequence with same size.

class sequence_simple_const extends uvm_common::sequence_base#(config_sequence, sequence_item);
    `uvm_object_utils(uvm_byte_array::sequence_simple_const)
    `uvm_declare_p_sequencer(uvm_byte_array::sequencer);

    rand int unsigned data_size;
    rand int unsigned transaction_count;

    constraint c1 {transaction_count inside {[cfg.transaction_count_min : cfg.transaction_count_max]};}
    constraint c2 {data_size inside {[cfg.array_size_min : cfg.array_size_max]};}

    // Constructor - creates new instance of this class
    function new(string name = "sequence_simple_const");
        super.new(name);
    endfunction

    // -----------------------
    // Functions.
    // -----------------------
    // Generates transactions
    task body;
        `uvm_info(get_full_name(), "\tsequence_simple_const is running", UVM_DEBUG)

        repeat(transaction_count)
        begin
            // Generate random request, which must be in interval from min length to max length
            `uvm_do_with(req, {data.size == data_size; });
        end
    endtask

endclass

// High level sequence with Gaussian distribution.

class sequence_simple_gauss extends uvm_common::sequence_base#(config_sequence, sequence_item);
    `uvm_object_utils(uvm_byte_array::sequence_simple_gauss)
    `uvm_declare_p_sequencer(uvm_byte_array::sequencer);

    rand int unsigned transaction_count;
    rand int unsigned mean; // Mean of data size
    rand int unsigned std_deviation; // Standard deviation
    int unsigned std_deviation_min = 1;
    int unsigned std_deviation_max = 32;

    constraint c1 {transaction_count inside {[cfg.transaction_count_min : cfg.transaction_count_max]};}
    constraint c2 {mean inside {[cfg.array_size_min : cfg.array_size_max]};}
    constraint c3 {std_deviation inside {[std_deviation_min : std_deviation_max]};}

    function int gaussian_dist();
        int unsigned value;
        value = $dist_normal($urandom(), mean, std_deviation);

        if (cfg.array_size_min < value && value < cfg.array_size_max) begin
            return value;
        end

        return mean;
    endfunction


    // Constructor - creates new instance of this class
    function new(string name = "sequence_simple_gauss");
        super.new(name);
    endfunction

    // -----------------------
    // Functions.
    // -----------------------
    // Generates transactions
    task body;
        int unsigned data_size;
        `uvm_info(get_full_name(), "sequence_simple_gauss is running", UVM_DEBUG)

        repeat(transaction_count)
        begin
            data_size = gaussian_dist();
            // Generate random request, which must be in interval from min length to max length
            `uvm_do_with(req, {data.size ==  data_size;});
        end
    endtask

endclass

// High level sequence with increment size.

class sequence_simple_inc extends uvm_common::sequence_base#(config_sequence, sequence_item);
    `uvm_object_utils(uvm_byte_array::sequence_simple_inc)
    `uvm_declare_p_sequencer(uvm_byte_array::sequencer);

    rand int unsigned transaction_count;
    rand int unsigned step;
    rand int unsigned data_size;
    int unsigned border = 4096;

    constraint c1 {transaction_count inside {[cfg.transaction_count_min : cfg.transaction_count_max]};}
    constraint c2 {step  inside {[1:16]};}
    constraint c3 {data_size inside {[cfg.array_size_min : cfg.array_size_max]};}

    // Constructor - creates new instance of this class
    function new(string name = "sequence_simple_inc");
        super.new(name);
    endfunction

    // -----------------------
    // Functions.
    // -----------------------
    // Generates transactions
    task body;
        int unsigned it;
        `uvm_info(get_full_name(), "sequence_simple_inc is running", UVM_DEBUG)

        it = 0;
        while (it < transaction_count && data_size <= cfg.array_size_max)begin
            // Generate random request, which must be in interval from min length to max length
            if (data_size <= border) begin
                `uvm_do_with(req, {data.size == data_size; });
                data_size += step;
            end else begin
                break;
            end

            it++;
        end
    endtask

endclass


// High level sequence with decrement size.

class sequence_simple_dec extends uvm_common::sequence_base#(config_sequence, sequence_item);
    `uvm_object_utils(uvm_byte_array::sequence_simple_dec)
    `uvm_declare_p_sequencer(uvm_byte_array::sequencer);

    rand int unsigned transaction_count;
    rand int unsigned step;
    rand int unsigned data_size;
    int unsigned border = 64;


    constraint c1 {transaction_count inside {[cfg.transaction_count_min : cfg.transaction_count_max]};}
    constraint c2 {step  inside {[1:16]};}
    constraint c3 {data_size inside {[cfg.array_size_min : cfg.array_size_max]};}

    // Constructor - creates new instance of this class
    function new(string name = "sequence_simple_dec");
        super.new(name);
    endfunction

    // -----------------------
    // Functions.
    // -----------------------

    // Generates transactions
    task body;
        int unsigned it;
        `uvm_info(get_full_name(), "sequence_simple_dec is running", UVM_DEBUG)

        it = 0;
        while (it < transaction_count && data_size >= cfg.array_size_min)begin
            // Generate random request, which must be in interval from min length to max length
            if (data_size >= border) begin
                `uvm_do_with(req, {data.size == data_size; });
                data_size -= step;
            end else begin
                break;
            end

            it++;
        end
    endtask

endclass

// High level sequence which is used for measuring
class sequence_simple_meas extends uvm_sequence #(sequence_item);
    `uvm_object_utils(uvm_byte_array::sequence_simple_meas)
    `uvm_declare_p_sequencer(uvm_byte_array::sequencer);

    int unsigned transaction_count = 370;
    int unsigned data_size    = 64;
    int unsigned step         = 4;
    int unsigned border       = 0;
    int unsigned biggest_size = 1500;
    int unsigned border_max   = 60*data_size;
    logic meas_done           = 0;

    // Constructor - creates new instance of this class
    function new(string name = "sequence_simple_meas");
        super.new(name);
    endfunction

    // -----------------------
    // Functions.
    // -----------------------

    // Generates transactions
    task body;
        `uvm_info(get_full_name(), "sequence_simple_meas is running", UVM_DEBUG)
        repeat (transaction_count)
        begin
            while (border <= border_max) begin
                `uvm_do_with(req, {data.size == data_size; });
                border += data_size;
            end
            data_size += step;
            border_max = 60*data_size;
            border = 0;
        end
    endtask

endclass


/////////////////////////////////////////////////////////////////////////
// SEQUENCE LIBRARY
class sequence_lib extends uvm_common::sequence_library#(config_sequence, sequence_item);
  `uvm_object_utils(uvm_byte_array::sequence_lib)
  `uvm_sequence_library_utils(uvm_byte_array::sequence_lib)

    function new(string name = "sequence_library");
        super.new(name);
        init_sequence_library();
    endfunction

    // subclass can redefine and change run sequences
    // can be useful in specific tests
    virtual function void init_sequence(config_sequence param_cfg = null);
        super.init_sequence(param_cfg);
        this.add_sequence(sequence_simple::get_type());
        this.add_sequence(sequence_simple_const::get_type());
        this.add_sequence(sequence_simple_gauss::get_type());
        this.add_sequence(sequence_simple_inc::get_type());
        this.add_sequence(sequence_simple_dec::get_type());
    endfunction
endclass
