//-- sequence.sv: AVST credit control sequence
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause 

class sequence_simple extends uvm_common::sequence_base #(config_sequence, sequence_item);
    `uvm_object_utils(uvm_crdt::sequence_simple)

    // ------------------------------------------------------------------------
    // Variables
    sequence_item req;

    int unsigned max_transaction_count = 100;
    int unsigned min_transaction_count = 10;
    rand int unsigned transaction_count;

    constraint c1 {transaction_count inside {[min_transaction_count: max_transaction_count]};}
    // ------------------------------------------------------------------------
    // Constructor
    function new(string name = "sequence_simple");
        super.new(name);
    endfunction

    task send_frame();
        start_item(req);
        void'(req.randomize() with {init_done == 1'b1;});
        finish_item(req);
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
        req = sequence_item::type_id::create("req");
        it = 0;
        while (it < transaction_count && (state == null || state.next())) begin
            // Create a request for sequence item
            send_frame();
            it++;
        end
    endtask
endclass

class sequence_stop extends uvm_common::sequence_base #(config_sequence, sequence_item);
    `uvm_object_utils(uvm_crdt::sequence_stop)

    // ------------------------------------------------------------------------
    // Variables
    sequence_item req;

    int unsigned max_transaction_count = 50;
    int unsigned min_transaction_count = 20;
    rand int unsigned transaction_count;

    constraint c1 {transaction_count inside {[min_transaction_count: max_transaction_count]};}
    // ------------------------------------------------------------------------
    // Constructor
    function new(string name = "sequence_stop");
        super.new(name);
    endfunction

    task send_frame();
        start_item(req);
        void'(req.randomize() with {init_done == 1'b0;});
        finish_item(req);
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
        req = sequence_item::type_id::create("req");
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
class sequence_lib extends uvm_common::sequence_library#(config_sequence, uvm_crdt::sequence_item);
  `uvm_object_utils(uvm_crdt::sequence_lib)
  `uvm_sequence_library_utils(uvm_crdt::sequence_lib)

  function new(string name = "sequence_lib");
    super.new(name);
    init_sequence_library();
  endfunction

    // subclass can redefine and change run sequences
    // can be useful in specific tests
    virtual function void init_sequence(config_sequence param_cfg = null);
        super.init_sequence(param_cfg);
        this.add_sequence(uvm_crdt::sequence_simple::get_type());
    endfunction
endclass

