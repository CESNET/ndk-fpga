/*
 * file       : sequence.sv
 * Copyright (C) 2022 CESNET z. s. p. o.
 * description: size_gen sequence
 * date       : 2022
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


// Reusable high level sequence. Contains transaction, which has only data part.
class sequence_simple #(int unsigned ITEM_WIDTH) extends uvm_common::sequence_base#(config_sequence, sequence_item#(ITEM_WIDTH));
    `ndk_object_param_utils(
        uvm_logic_vector_array::sequence_simple#(ITEM_WIDTH),
        $sformatf("uvm_logic_vector_array::sequence_simple#(%0d)",ITEM_WIDTH)
    )
    `uvm_declare_p_sequencer(uvm_logic_vector_array::sequencer#(ITEM_WIDTH));

    int unsigned transaction_count_min = 10;
    int unsigned transaction_count_max = 200;
    rand int unsigned transaction_count;

    rand int unsigned data_size_min;
    rand int unsigned data_size_max;

    constraint c1 {transaction_count inside {[transaction_count_min : transaction_count_max]};}
    constraint c_data_size {
        data_size_min <= data_size_max;
        data_size_min dist {
             cfg.array_size_min :/ 5,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*0 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*1] :/ 20,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*1 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*2] :/ 7,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*2 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*3] :/ 5,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*3 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*4] :/ 3,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*4 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*5] :/ 2,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*5 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*6] :/ 1,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*6 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*7] :/ 1,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*7 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*8] :/ 3,
             cfg.array_size_max :/ 5
        };

        data_size_max dist {
             cfg.array_size_min :/ 5,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*0 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*1] :/ 20,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*1 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*2] :/ 7,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*2 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*3] :/ 5,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*3 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*4] :/ 3,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*4 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*5] :/ 2,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*5 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*6] :/ 1,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*6 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*7] :/ 1,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*7 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*8] :/ 3,
             cfg.array_size_max :/ 5
        };

    }

    // Constructor - creates new instance of this class
    function new(string name = "sequence_simple");
        super.new(name);
    endfunction

    // -----------------------
    // Functions.
    // -----------------------
    task body;
        int unsigned it;
        uvm_common::sequence_cfg state;

        if(!uvm_config_db#(uvm_common::sequence_cfg)::get(m_sequencer, "", "state", state)) begin
            state = null;
        end

        `uvm_info(m_sequencer.get_full_name(), "\n\tsequence_simple is running", UVM_DEBUG)

        it = 0;
        while(it < transaction_count && (state == null || state.next()))
        begin
            // Generate random request, which must be in interval from min length to max length
            `uvm_do_with(req, {data.size inside{[data_size_min : data_size_max]}; });
            it++;
        end
    endtask
endclass

// High level sequence with same size.

class sequence_simple_const #(int unsigned ITEM_WIDTH) extends uvm_common::sequence_base#(config_sequence, sequence_item#(ITEM_WIDTH));
    `ndk_object_param_utils(
        uvm_logic_vector_array::sequence_simple_const#(ITEM_WIDTH),
        $sformatf("uvm_logic_vector_array::sequence_simple_const#(%0d)",ITEM_WIDTH)
    )
    `uvm_declare_p_sequencer(uvm_logic_vector_array::sequencer#(ITEM_WIDTH));

    int unsigned transaction_count_min = 10;
    int unsigned transaction_count_max = 200;

    rand int unsigned data_size;
    rand int unsigned transaction_count;

    constraint c1 {transaction_count inside {[transaction_count_min : transaction_count_max]};}
    constraint c2 {data_size dist {
             cfg.array_size_min :/ 5,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*0 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*1] :/ 20,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*1 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*2] :/ 7,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*2 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*3] :/ 5,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*3 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*4] :/ 3,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*4 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*5] :/ 2,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*5 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*6] :/ 1,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*6 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*7] :/ 1,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*7 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*8] :/ 3,
             cfg.array_size_max :/ 5
        };}

    // Constructor - creates new instance of this class
    function new(string name = "sequence_simple_const");
        super.new(name);
    endfunction

    // -----------------------
    // Functions.
    // -----------------------
    // Generates transactions
    task body;
        int unsigned it;
        uvm_common::sequence_cfg state;

        if(!uvm_config_db#(uvm_common::sequence_cfg)::get(m_sequencer, "", "state", state)) begin
            state = null;
        end

        `uvm_info(m_sequencer.get_full_name(), "\n\tsequence_simple_const is running", UVM_DEBUG)
        it = 0;
        while(it < transaction_count && (state == null || state.next()))
        begin
            // Generate random request, which must be in interval from min length to max length
            `uvm_do_with(req, {data.size == data_size; });
            it++;
        end
        `uvm_info(m_sequencer.get_full_name(), "\n\tsequence_simple_const is ending", UVM_DEBUG)
    endtask

endclass

// High level sequence with Gaussian distribution.

class sequence_simple_gauss #(int unsigned ITEM_WIDTH) extends uvm_common::sequence_base#(config_sequence, sequence_item#(ITEM_WIDTH));
    `ndk_object_param_utils(
        uvm_logic_vector_array::sequence_simple_gauss#(ITEM_WIDTH),
        $sformatf("uvm_logic_vector_array::sequence_simple_gauss#(%0d)",ITEM_WIDTH)
    )
    `uvm_declare_p_sequencer(uvm_logic_vector_array::sequencer#(ITEM_WIDTH));

    int unsigned transaction_count_min = 10;
    int unsigned transaction_count_max = 200;

    rand int unsigned transaction_count;
    rand int unsigned mean; // Mean of data size
    rand int unsigned std_deviation; // Standard deviation
    int unsigned std_deviation_min = 1;
    int unsigned std_deviation_max = 32;

    constraint c1 {transaction_count inside {[transaction_count_min : transaction_count_max]};}
    constraint c2 {
        mean dist {
             cfg.array_size_min :/ 5,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*0 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*1] :/ 20,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*1 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*2] :/ 7,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*2 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*3] :/ 5,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*3 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*4] :/ 3,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*4 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*5] :/ 2,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*5 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*6] :/ 1,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*6 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*7] :/ 1,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*7 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*8] :/ 3,
             cfg.array_size_max :/ 5
        };
    }
    constraint c3 {std_deviation inside {[std_deviation_min : std_deviation_max]};}

    function int gaussian_dist();
        int unsigned value;
        // verilog_lint: waive invalid-system-task-function
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
        int unsigned it;
        int unsigned data_size;
        uvm_common::sequence_cfg state;

        if(!uvm_config_db#(uvm_common::sequence_cfg)::get(m_sequencer, "", "state", state)) begin
            state = null;
        end

        `uvm_info(m_sequencer.get_full_name(), "\n\tsequence_simple_gauss is running", UVM_DEBUG)
        it = 0;
        while(it < transaction_count && (state == null || state.next()))
        begin
            data_size = gaussian_dist();
            // Generate random request, which must be in interval from min length to max length
            `uvm_do_with(req, {data.size ==  data_size;});
            it++;
        end
    endtask

endclass

// High level sequence with increment size.

class sequence_simple_inc #(int unsigned ITEM_WIDTH) extends uvm_common::sequence_base#(config_sequence, sequence_item#(ITEM_WIDTH));
    `ndk_object_param_utils(
        uvm_logic_vector_array::sequence_simple_inc#(ITEM_WIDTH),
        $sformatf("uvm_logic_vector_array::sequence_simple_inc#(%0d)",ITEM_WIDTH)
    )
    `uvm_declare_p_sequencer(uvm_logic_vector_array::sequencer#(ITEM_WIDTH));

    int unsigned transaction_count_min = 10;
    int unsigned transaction_count_max = 200;

    rand int unsigned transaction_count;
    rand int unsigned step;
    rand int unsigned data_size;
    int unsigned border = 4096;

    constraint c1 {transaction_count inside {[transaction_count_min : transaction_count_max]};}
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
        uvm_common::sequence_cfg state;

        if(!uvm_config_db#(uvm_common::sequence_cfg)::get(m_sequencer, "", "state", state)) begin
            state = null;
        end

        `uvm_info(m_sequencer.get_full_name(), "\n\tsequence_simple_inc is running", UVM_DEBUG)
        it = 0;
        while (it < transaction_count && data_size <= cfg.array_size_max && data_size <= border && (state == null || state.next()))begin
            // Generate random request, which must be in interval from min length to max length
            `uvm_do_with(req, {data.size == data_size; });
            data_size += step;

            it++;
        end
    endtask

endclass


// High level sequence with decrement size.

class sequence_simple_dec #(int unsigned ITEM_WIDTH) extends uvm_common::sequence_base#(config_sequence, sequence_item#(ITEM_WIDTH));
    `ndk_object_param_utils(
        uvm_logic_vector_array::sequence_simple_dec#(ITEM_WIDTH),
        $sformatf("uvm_logic_vector_array::sequence_simple_dec#(%0d)",ITEM_WIDTH)
    )
    `uvm_declare_p_sequencer(uvm_logic_vector_array::sequencer#(ITEM_WIDTH));

    int unsigned transaction_count_min = 10;
    int unsigned transaction_count_max = 200;

    rand int unsigned transaction_count;
    rand int unsigned step;
    rand int unsigned data_size;
    int unsigned border = 64;


    constraint c1 {transaction_count inside {[transaction_count_min : transaction_count_max]};}
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
        uvm_common::sequence_cfg state;

        if(!uvm_config_db#(uvm_common::sequence_cfg)::get(m_sequencer, "", "state", state)) begin
            state = null;
        end
        `uvm_info(m_sequencer.get_full_name(), "\n\tsequence_simple_dec is running", UVM_DEBUG)

        it = 0;
        while (it < transaction_count && data_size >= cfg.array_size_min && data_size >= border && (state == null || state.next()))begin
            // Generate random request, which must be in interval from min length to max length
            `uvm_do_with(req, {data.size == data_size; });
            data_size -= step;

            it++;
        end
    endtask

endclass

// High level sequence which is used for measuring
class sequence_simple_meas #(int unsigned ITEM_WIDTH) extends uvm_common::sequence_base#(sequence_item#(ITEM_WIDTH));
    `ndk_object_param_utils(
        uvm_logic_vector_array::sequence_simple_meas#(ITEM_WIDTH),
        $sformatf("uvm_logic_vector_array::sequence_simple_meas#(%0d)",ITEM_WIDTH)
    );
    `uvm_declare_p_sequencer(uvm_logic_vector_array::sequencer#(ITEM_WIDTH));

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
        int unsigned it;
        uvm_common::sequence_cfg state;

        if(!uvm_config_db#(uvm_common::sequence_cfg)::get(m_sequencer, "", "state", state)) begin
            state = null;
        end
        `uvm_info(m_sequencer.get_full_name(), "\n\tsequence_simple_meas is running", UVM_DEBUG)

        it = 0;
        while(it < transaction_count && (state == null || state.next())) begin
            while (border <= border_max && (state == null || state.next())) begin
                `uvm_do_with(req, {data.size == data_size; });
                border += data_size;
            end
            data_size += step;
            border_max = 60*data_size;
            border = 0;

            it++;
        end
    endtask

endclass

class sequence_min_max #(int unsigned ITEM_WIDTH) extends sequence_simple #(ITEM_WIDTH);
    `ndk_object_param_utils(
        uvm_logic_vector_array::sequence_min_max#(ITEM_WIDTH),
        $sformatf("uvm_logic_vector_array::sequence_min_max#(%0d)",ITEM_WIDTH)
    )

    // Constructor
    function new(string name = "sequence_min_max");
        super.new(name);
    endfunction

    task body;
        uvm_common::sequence_cfg state;
        void'(uvm_config_db #(uvm_common::sequence_cfg)::get(m_sequencer, "", "state", state));

        `uvm_info(m_sequencer.get_full_name(), "\n\tsequence_min_max is running", UVM_DEBUG)

        repeat (transaction_count) begin
            if (state != null) begin
                if (!state.next()) begin
                    break;
                end
            end

            `uvm_do_with(req, {
                data.size inside { cfg.array_size_min, cfg.array_size_max };
            });
        end
    endtask

endclass

class sequence_inverted_gauss #(int unsigned ITEM_WIDTH) extends sequence_simple #(ITEM_WIDTH);
    `ndk_object_param_utils(
        uvm_logic_vector_array::sequence_inverted_gauss#(ITEM_WIDTH),
        $sformatf("uvm_logic_vector_array::sequence_inverted_gauss#(%0d)",ITEM_WIDTH)
    )

    int unsigned mean;
    rand int unsigned data_size_min;
    rand int unsigned data_size_max;

    constraint c_data_size {
        data_size_min <= data_size_max;
        data_size_min dist {
             cfg.array_size_min :/ 5,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*0 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*1] :/ 20,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*1 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*2] :/ 7,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*2 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*3] :/ 5,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*3 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*4] :/ 3,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*4 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*5] :/ 2,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*5 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*6] :/ 1,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*6 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*7] :/ 1,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*7 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*8] :/ 3,
             cfg.array_size_max :/ 5
        };

        data_size_max dist {
             cfg.array_size_min :/ 5,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*0 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*1] :/ 20,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*1 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*2] :/ 7,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*2 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*3] :/ 5,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*3 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*4] :/ 3,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*4 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*5] :/ 2,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*5 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*6] :/ 1,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*6 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*7] :/ 1,
            [cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*7 : cfg.array_size_min + (cfg.array_size_max-cfg.array_size_min)/8*8] :/ 3,
             cfg.array_size_max :/ 5
        };

    }


    // Constructor
    function new(string name = "sequence_inverted_gauss");
        super.new(name);
    endfunction

    function int math_min(int first, int second);
        return (first < second) ? first : second;
    endfunction

    function int math_max(int first, int second);
        return (first > second) ? first : second;
    endfunction

    function int inverted_gaussian_dist();
        // verilog_lint: waive invalid-system-task-function
        int value = $dist_normal($urandom(), mean, mean/3);
        value = math_min(value, data_size_max);
        value = math_max(value, data_size_min);

        if (value < mean) begin
            return math_min(value+mean, data_size_max);
        end
        else begin
            return math_max(value-mean, data_size_min);
        end
    endfunction

    task body;
        uvm_common::sequence_cfg state;
        void'(uvm_config_db #(uvm_common::sequence_cfg)::get(m_sequencer, "", "state", state));

        `uvm_info(m_sequencer.get_full_name(), "\n\tsequence_inverted_gauss is running", UVM_DEBUG)

        mean = (data_size_max-data_size_min)/2;

        repeat (transaction_count) begin
            int unsigned data_size;

            if (state != null) begin
                if (!state.next()) begin
                    break;
                end
            end

            data_size = inverted_gaussian_dist();

            `uvm_do_with(req, {
                data.size == data_size;
            })
        end
    endtask

endclass

/////////////////////////////////////////////////////////////////////////
// SEQUENCE LIBRARY
class sequence_lib #(int unsigned ITEM_WIDTH) extends uvm_common::sequence_library#(config_sequence, sequence_item#(ITEM_WIDTH));
  `ndk_object_param_utils(
        uvm_logic_vector_array::sequence_lib#(ITEM_WIDTH),
        $sformatf("uvm_logic_vector_array::sequence_lib#(%0d)",ITEM_WIDTH)
    )
  `uvm_sequence_library_utils(uvm_logic_vector_array::sequence_lib#(ITEM_WIDTH))

    function new(string name = "sequence_library");
        super.new(name);
        init_sequence_library();
    endfunction

    // subclass can redefine and change run sequences
    // can be useful in specific tests
    virtual function void init_sequence(config_sequence param_cfg = null);
        super.init_sequence(param_cfg);
        this.add_sequence(sequence_simple         #(ITEM_WIDTH)::get_type());
        this.add_sequence(sequence_simple_const   #(ITEM_WIDTH)::get_type());
        this.add_sequence(sequence_simple_gauss   #(ITEM_WIDTH)::get_type());
        this.add_sequence(sequence_simple_inc     #(ITEM_WIDTH)::get_type());
        this.add_sequence(sequence_simple_dec     #(ITEM_WIDTH)::get_type());
        this.add_sequence(sequence_min_max        #(ITEM_WIDTH)::get_type());
        this.add_sequence(sequence_inverted_gauss #(ITEM_WIDTH)::get_type());
    endfunction
endclass
