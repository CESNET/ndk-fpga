/*
 * file       : sequence.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: base sequence Intel seq mac agent
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


class sequence_simple_rx #(int unsigned SEGMENTS) extends uvm_sequence #(sequence_item #(SEGMENTS));
    `ndk_object_param_utils(
        uvm_intel_mac_seg::sequence_simple_rx#(SEGMENTS),
        $sformatf("uvm_intel_mac_seg::sequence_simple_rx#(%0d)",SEGMENTS)
    )

    // ------------------------------------------------------------------------
    // Variables
    sequence_item #(SEGMENTS) req;

    int unsigned max_transaction_count = 2048;
    int unsigned min_transaction_count = 32;
    rand int unsigned transaction_count;

    constraint c1 {transaction_count inside {[min_transaction_count: max_transaction_count]};}
    // ------------------------------------------------------------------------
    // Constructor
    function new(string name = "sequence_simple_rx");
        super.new(name);
    endfunction

    task send_empty_frame();
        start_item(req);
        req.randomize();
        {>>{req.inframe}} = '0;
        req.valid   = '0;
        finish_item(req);
        get_response(rsp);
    endtask

    task send_frame();
        start_item(req);
        req.randomize();
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
        req = sequence_item #(SEGMENTS)::type_id::create("req");
        it = 0;
        while (it < transaction_count && (state == null || state.next())) begin
            // Create a request for sequence item
            send_frame();
            it++;
        end
    endtask
endclass


class sequence_simple_tx #(
    int unsigned SEGMENTS
) extends uvm_common::sequence_base #(config_sequence, sequence_item #(SEGMENTS));
    `ndk_object_param_utils(
        uvm_intel_mac_seg::sequence_simple_tx#(SEGMENTS),
        $sformatf("uvm_intel_mac_seg::sequence_simple_tx#(%0d)",SEGMENTS)
    )

    // ------------------------------------------------------------------------
    // Variables
    sequence_item #(SEGMENTS) req;
    uvm_common::rand_rdy          rdy;

    int unsigned max_transaction_count = 2048;
    int unsigned min_transaction_count = 32;
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
        void'(req.randomize() with {ready == rdy.m_value;});
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
        req = sequence_item #(SEGMENTS)::type_id::create("req");
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
class sequence_lib_tx #(
    int unsigned SEGMENTS
) extends uvm_common::sequence_library #(config_sequence, sequence_item #(SEGMENTS));
  `ndk_object_param_utils(
        uvm_intel_mac_seg::sequence_lib_tx#(SEGMENTS),
        $sformatf("uvm_intel_mac_seg::sequence_lib_tx#(%0d)",SEGMENTS)
    )
  `uvm_sequence_library_utils(uvm_intel_mac_seg::sequence_lib_tx#(SEGMENTS))

  function new(string name = "sequence_lib_tx");
    super.new(name);
    init_sequence_library();
  endfunction

    // subclass can redefine and change run sequences
    // can be useful in specific tests
    virtual function void init_sequence(config_sequence param_cfg = null);
        uvm_common::sequence_library::init_sequence(param_cfg);
        this.add_sequence(uvm_intel_mac_seg::sequence_simple_tx#(SEGMENTS)::get_type());
    endfunction
endclass



