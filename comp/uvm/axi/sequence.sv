//-- sequence.sv: AXI sequence
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class sequence_simple_tx #(int unsigned DATA_WIDTH, int unsigned TUSER_WIDTH, int unsigned REGIONS) extends uvm_common::sequence_base #(config_sequence, uvm_axi::sequence_item #(DATA_WIDTH, TUSER_WIDTH, REGIONS));
    `uvm_object_param_utils(uvm_axi::sequence_simple_tx #(DATA_WIDTH, TUSER_WIDTH, REGIONS))

    // ------------------------------------------------------------------------
    // Variables
    sequence_item #(DATA_WIDTH, TUSER_WIDTH, REGIONS) req;
    uvm_common::rand_rdy          rdy;

    int unsigned max_transaction_count = 100;
    int unsigned min_transaction_count = 10;
    rand int unsigned transaction_count;

    constraint c1 {transaction_count inside {[min_transaction_count: max_transaction_count]};}
    // ------------------------------------------------------------------------
    // Constructor
    function new(string name = "sequence_simple_tx");
        super.new(name);
        rdy = uvm_common::rand_rdy_rand::new();
    endfunction

    task send_frame();
        start_item(req);
        void'(rdy.randomize());
        void'(req.randomize() with {tready == rdy.m_value;});
        finish_item(req);
        get_response(rsp);
    endtask


    // ------------------------------------------------------------------------
    // Generates transactions
    task body;
        int unsigned it;
        uvm_common::sequence_cfg state;

        if(!uvm_config_db#(uvm_common::sequence_cfg)::get(m_sequencer, "", "state", state)) begin
            state = null;
        end
        rdy.bound_set(cfg.rdy_probability_min, cfg.rdy_probability_max);

        // Generate transaction_count transactions
        req = sequence_item #(DATA_WIDTH, TUSER_WIDTH, REGIONS)::type_id::create("req");
        it = 0;
        while (it < transaction_count && (state == null || state.next())) begin
            // Create a request for sequence item
            send_frame();
            it++;
        end
    endtask
endclass

class sequence_full_speed_tx #(int unsigned DATA_WIDTH, int unsigned TUSER_WIDTH, int unsigned REGIONS) extends uvm_common::sequence_base #(config_sequence, sequence_item #(DATA_WIDTH, TUSER_WIDTH, REGIONS));
    `uvm_object_param_utils(uvm_axi::sequence_full_speed_tx #(DATA_WIDTH, TUSER_WIDTH, REGIONS))

    // ------------------------------------------------------------------------
    // Variables
    sequence_item #(DATA_WIDTH, TUSER_WIDTH, REGIONS) req;

    int unsigned max_transaction_count = 100;
    int unsigned min_transaction_count = 10;
    rand int unsigned transaction_count;

    constraint c1 {transaction_count inside {[min_transaction_count: max_transaction_count]};}
    // ------------------------------------------------------------------------
    // Constructor
    function new(string name = "sequence_full_speed_tx");
        super.new(name);
    endfunction

    task send_frame();
        start_item(req);
        void'(req.randomize() with {tready == 1'b1;});
        finish_item(req);
        get_response(rsp);
    endtask


    // ------------------------------------------------------------------------
    // Generates transactions
    task body;
        int unsigned it;
        uvm_common::sequence_cfg state;

        if(!uvm_config_db#(uvm_common::sequence_cfg)::get(m_sequencer, "", "state", state)) begin
            state = null;
        end
        // Generate transaction_count transactions
        req = sequence_item #(DATA_WIDTH, TUSER_WIDTH, REGIONS)::type_id::create("req");
        it = 0;
        while (it < transaction_count && (state == null || state.next())) begin
            // Create a request for sequence item
            send_frame();
            it++;
        end
    endtask
endclass

class sequence_stop_tx #(int unsigned DATA_WIDTH, int unsigned TUSER_WIDTH, int unsigned REGIONS) extends uvm_common::sequence_base #(config_sequence, sequence_item #(DATA_WIDTH, TUSER_WIDTH, REGIONS));
    `uvm_object_param_utils(uvm_axi::sequence_stop_tx #(DATA_WIDTH, TUSER_WIDTH, REGIONS))

    // ------------------------------------------------------------------------
    // Variables
    sequence_item #(DATA_WIDTH, TUSER_WIDTH, REGIONS) req;

    int unsigned max_transaction_count = 50;
    int unsigned min_transaction_count = 10;
    rand int unsigned transaction_count;

    constraint c1 {transaction_count inside {[min_transaction_count: max_transaction_count]};}
    // ------------------------------------------------------------------------
    // Constructor
    function new(string name = "sequence_stop_tx");
        super.new(name);
    endfunction

    task send_frame();
        start_item(req);
        void'(req.randomize() with {tready == 1'b0;});
        finish_item(req);
        get_response(rsp);
    endtask


    // ------------------------------------------------------------------------
    // Generates transactions
    task body;
        int unsigned it;
        uvm_common::sequence_cfg state;

        if(!uvm_config_db#(uvm_common::sequence_cfg)::get(m_sequencer, "", "state", state)) begin
            state = null;
        end
        // Generate transaction_count transactions
        req = sequence_item #(DATA_WIDTH, TUSER_WIDTH, REGIONS)::type_id::create("req");
        it = 0;
        while (it < transaction_count && (state == null || state.next())) begin
            // Create a request for sequence item
            send_frame();
            it++;
        end
    endtask
endclass


/////////////////////////////////////////////////////////////////////////
// SEQUENCE LIBRARY RX
class sequence_lib_tx #(int unsigned DATA_WIDTH, int unsigned TUSER_WIDTH, int unsigned REGIONS) extends uvm_common::sequence_library#(config_sequence, uvm_axi::sequence_item #(DATA_WIDTH, TUSER_WIDTH, REGIONS));
  `uvm_object_param_utils(uvm_axi::sequence_lib_tx#(DATA_WIDTH, TUSER_WIDTH, REGIONS))
  `uvm_sequence_library_utils(uvm_axi::sequence_lib_tx#(DATA_WIDTH, TUSER_WIDTH, REGIONS))

  function new(string name = "sequence_lib_tx");
    super.new(name);
    init_sequence_library();
  endfunction

    // subclass can redefine and change run sequences
    // can be useful in specific tests
    virtual function void init_sequence(config_sequence param_cfg = null);
        super.init_sequence(param_cfg);
        this.add_sequence(uvm_axi::sequence_simple_tx #(DATA_WIDTH, TUSER_WIDTH, REGIONS)::get_type());
        this.add_sequence(uvm_axi::sequence_full_speed_tx #(DATA_WIDTH, TUSER_WIDTH, REGIONS)::get_type());
        this.add_sequence(uvm_axi::sequence_stop_tx #(DATA_WIDTH, TUSER_WIDTH, REGIONS)::get_type());
    endfunction
endclass

