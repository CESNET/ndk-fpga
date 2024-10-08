//-- sequence.sv: Mvb sequence
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef MVB_SEQUENCE_SV
`define MVB_SEQUENCE_SV

// This low level sequence define bus functionality
class sequence_simple_rx #(int unsigned ITEMS, int unsigned ITEM_WIDTH) extends uvm_sequence #(uvm_mvb::sequence_item #(ITEMS, ITEM_WIDTH));
    `uvm_object_param_utils(uvm_mvb::sequence_simple_rx #(ITEMS, ITEM_WIDTH))

    // ------------------------------------------------------------------------
    // Variables
    sequence_item #(ITEMS, ITEM_WIDTH) req;

    int unsigned transaction_count_max = 100;
    int unsigned transaction_count_min = 10;
    rand int unsigned transaction_count;

    constraint tr_cnt_cons {transaction_count inside {[transaction_count_min:transaction_count_max]};}
    // ------------------------------------------------------------------------
    // Constructor
    function new(string name = "Simple_sequence_rx");
        super.new(name);
    endfunction

    // ------------------------------------------------------------------------
    // Generates transactions
    task body;
        int unsigned it;
        uvm_common::sequence_cfg state;

        if(!uvm_config_db#(uvm_common::sequence_cfg)::get(m_sequencer, "", "state", state)) begin
            state = null;
        end

        // Generate transaction_count transactions
        req = sequence_item #(ITEMS, ITEM_WIDTH)::type_id::create("req");

        it = 0;
        while (it < transaction_count && (state == null || state.next())) begin
            start_item(req);

            if (!req.randomize()) begin
                `uvm_fatal("sequence:", "Faile to randomize sequence.")
            end
            finish_item(req);
            get_response(rsp);


            while (rsp.src_rdy && !rsp.dst_rdy) begin
                start_item(req);
                finish_item(req);

                get_response(rsp);
            end
            it++;
        end
    endtask
endclass

//////////////////////////////////////
// RX LIBRARY
class sequence_lib_rx #(int unsigned ITEMS, int unsigned ITEM_WIDTH) extends uvm_sequence_library#(uvm_mvb::sequence_item#(ITEMS, ITEM_WIDTH));
  `uvm_object_param_utils(uvm_mvb::sequence_lib_rx#(ITEMS, ITEM_WIDTH))
  `uvm_sequence_library_utils(uvm_mvb::sequence_lib_rx#(ITEMS, ITEM_WIDTH))

    function new(string name = "sequence_lib_rx");
        super.new(name);
        init_sequence_library();
    endfunction

    // subclass can redefine and change run sequences
    // can be useful in specific tests
    virtual function void init_sequence();
        this.add_sequence(sequence_simple_rx#(ITEMS, ITEM_WIDTH)::get_type());
    endfunction
endclass

// This low level sequence define how can data looks like
class sequence_simple_tx #(int unsigned ITEMS, int unsigned ITEM_WIDTH) extends uvm_common::sequence_base#(config_sequence, uvm_mvb::sequence_item #(ITEMS, ITEM_WIDTH));

    // ------------------------------------------------------------------------
    // Registration of agent to databaze
    `uvm_object_param_utils(uvm_mvb::sequence_simple_tx #(ITEMS, ITEM_WIDTH))

    // ------------------------------------------------------------------------
    // Variables
    sequence_item #(ITEMS, ITEM_WIDTH) req;
    uvm_common::rand_rdy          rdy;

    int unsigned max_transaction_count = 100;
    int unsigned min_transaction_count = 10;
    rand int unsigned transaction_count;

    constraint c1 {transaction_count inside {[min_transaction_count: max_transaction_count]};}

    // ------------------------------------------------------------------------
    // Constructor
    function new(string name = "Simple_sequence_tx");
        super.new(name);
        rdy = uvm_common::rand_rdy_rand::new();
    endfunction

    // ------------------------------------------------------------------------
    // Generates transactions
    task body();
        int unsigned it;
        uvm_common::sequence_cfg state;

        `uvm_info(m_sequencer.get_full_name(), "\n\tuvm_mvb::sequence_simple_tx is running", UVM_DEBUG);
        if(!uvm_config_db#(uvm_common::sequence_cfg)::get(m_sequencer, "", "state", state)) begin
            state = null;
        end

        // Generate transaction_count transactions
        req = sequence_item#(ITEMS, ITEM_WIDTH)::type_id::create("req");
        it = 0;
        while(it < transaction_count && (state == null || state.next())) begin
            // Create a request for sequence item
            start_item(req);
            void'(rdy.randomize());
            void'(req.randomize() with {dst_rdy == rdy.m_value;});
            finish_item(req);
            get_response(rsp);

            it++;
        end
    endtask

    virtual function void config_set(CONFIG_TYPE cfg);
        super.config_set(cfg);
        rdy.bound_set(cfg.rdy_probability_min, cfg.rdy_probability_max);
    endfunction
endclass


// This low level sequence that have every tact dst rdy at tx side
class sequence_full_speed_tx #(int unsigned ITEMS, int unsigned ITEM_WIDTH) extends uvm_common::sequence_base#(config_sequence, uvm_mvb::sequence_item #(ITEMS, ITEM_WIDTH));
    `uvm_object_param_utils(uvm_mvb::sequence_full_speed_tx #(ITEMS, ITEM_WIDTH))

    // ------------------------------------------------------------------------
    // Variables
    sequence_item #(ITEMS, ITEM_WIDTH) req;
    int unsigned max_transaction_count = 100;
    int unsigned min_transaction_count = 10;
    rand int unsigned transaction_count;

    constraint c1 {transaction_count inside {[min_transaction_count: max_transaction_count]};}

    // ------------------------------------------------------------------------
    // Constructor
    function new(string name = "sequence_full_speed_tx");
        super.new(name);
    endfunction

    // ------------------------------------------------------------------------
    // Generates transactions
    task body;
        int unsigned it;
        uvm_common::sequence_cfg state;

        `uvm_info(m_sequencer.get_full_name(), "\n\tuvm_mvb::sequence_full_speed_tx is running", UVM_DEBUG);
        if(!uvm_config_db#(uvm_common::sequence_cfg)::get(m_sequencer, "", "state", state)) begin
            state = null;
        end

        req = sequence_item#(ITEMS, ITEM_WIDTH)::type_id::create("req");
        it = 0;
        while (it < transaction_count && (state == null || state.next())) begin
            // Create a request for sequence item
            start_item(req);
            void'(req.randomize() with {dst_rdy == 1'b1;});
            finish_item(req);
            get_response(rsp);
            it++;
        end
    endtask

endclass

class sequence_stop_tx #(int unsigned ITEMS, int unsigned ITEM_WIDTH) extends uvm_common::sequence_base#(config_sequence, uvm_mvb::sequence_item #(ITEMS, ITEM_WIDTH));
    `uvm_object_param_utils(uvm_mvb::sequence_stop_tx #(ITEMS, ITEM_WIDTH))

    // ------------------------------------------------------------------------
    // Variables
    sequence_item #(ITEMS, ITEM_WIDTH) req;
    int unsigned max_transaction_count = 50;
    int unsigned min_transaction_count = 10;
    rand int unsigned transaction_count;

    constraint c1 {transaction_count inside {[min_transaction_count: max_transaction_count]};}

    // ------------------------------------------------------------------------
    // Constructor
    function new(string name = "sequence_stop_tx");
        super.new(name);
    endfunction

    // ------------------------------------------------------------------------
    // Generates transactions
    task body;
        int unsigned it;
        uvm_common::sequence_cfg state;

        `uvm_info(m_sequencer.get_full_name(), "\n\tuvm_mvb::sequence_stop_tx is running", UVM_DEBUG);

        if(!uvm_config_db#(uvm_common::sequence_cfg)::get(m_sequencer, "", "state", state)) begin
            state = null;
        end
        // Generate transaction_count transactions
        req = sequence_item#(ITEMS, ITEM_WIDTH)::type_id::create("req");
        it = 0;
        while (it < transaction_count && (state == null || state.next())) begin
            // Create a request for sequence item
            start_item(req);
            void'(req.randomize() with {dst_rdy == 1'b0;});
            finish_item(req);
            get_response(rsp);

            it++;
        end

    endtask

endclass



//////////////////////////////////////
// TX LIBRARY
class sequence_lib_tx #(int unsigned ITEMS, int unsigned ITEM_WIDTH) extends uvm_common::sequence_library#(config_sequence, sequence_item#(ITEMS, ITEM_WIDTH));
  `uvm_object_param_utils(uvm_mvb::sequence_lib_tx#(ITEMS, ITEM_WIDTH))
  `uvm_sequence_library_utils(uvm_mvb::sequence_lib_tx#(ITEMS, ITEM_WIDTH))

    function new(string name = "sequence_lib_tx");
        super.new(name);
        init_sequence_library();
    endfunction

    // subclass can redefine and change run sequences
    // can be useful in specific tests
    virtual function void init_sequence(config_sequence param_cfg = null);
        uvm_common::sequence_library::init_sequence(param_cfg);
        this.add_sequence(sequence_simple_tx#(ITEMS, ITEM_WIDTH)::get_type());
        this.add_sequence(sequence_full_speed_tx#(ITEMS, ITEM_WIDTH)::get_type());
        this.add_sequence(sequence_stop_tx#(ITEMS, ITEM_WIDTH)::get_type());
    endfunction
endclass


class sequence_lib_tx_speed #(int unsigned ITEMS, int unsigned ITEM_WIDTH) extends sequence_lib_tx#(ITEMS, ITEM_WIDTH);
  `uvm_object_param_utils(    uvm_mvb::sequence_lib_tx_speed#(ITEMS, ITEM_WIDTH))
  `uvm_sequence_library_utils(uvm_mvb::sequence_lib_tx_speed#(ITEMS, ITEM_WIDTH))

    function new(string name = "sequence_lib_tx_speed");
        super.new(name);
        init_sequence_library();
    endfunction

    // subclass can redefine and change run sequences
    // can be useful in specific tests
    virtual function void init_sequence(config_sequence param_cfg = null);
        uvm_common::sequence_library::init_sequence(param_cfg);
        this.add_sequence(uvm_mvb::sequence_full_speed_tx#(ITEMS, ITEM_WIDTH)::get_type());
    endfunction
endclass


`endif
