// sequence.sv: Virtual sequence
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kondys <xkondy00@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class meta_sequence #(META_WIDTH, CHANNELS) extends uvm_sequence#(uvm_logic_vector::sequence_item#(META_WIDTH));
    `uvm_object_param_utils(test::meta_sequence #(META_WIDTH, CHANNELS));

    function new (string name = "meta_sequence");
        super.new(name);
    endfunction

    task body();
        forever begin
            req = uvm_logic_vector::sequence_item#(META_WIDTH)::type_id::create("req");

            start_item(req);
            //                                                   +ETH_TX_HDR_PORT_O (channel offset)
            assert(req.randomize() with {data[$clog2(CHANNELS)-1 +16: 0 +16] inside {[0: CHANNELS-1]}; }); // comment this line if CHANNELS == 1
            finish_item(req);
        end
    endtask
endclass


class virt_seq #(ITEM_WIDTH, META_WIDTH, CHANNELS) extends uvm_sequence;
    `uvm_object_param_utils(test::virt_seq #(ITEM_WIDTH, META_WIDTH, CHANNELS))
    `uvm_declare_p_sequencer(uvm_logic_vector_array_mfb::sequencer_rx#(ITEM_WIDTH, META_WIDTH))

    function new (string name = "virt_seq");
        super.new(name);
    endfunction

    uvm_logic_vector_array::sequence_lib#(ITEM_WIDTH) m_byte_array_seq;
    meta_sequence #(META_WIDTH, CHANNELS) m_logic_vector_seq;

    task pre_body();
        m_byte_array_seq   = uvm_logic_vector_array::sequence_lib#(ITEM_WIDTH)::type_id::create("m_byte_array_seq");
        m_byte_array_seq.init_sequence();
        m_byte_array_seq.min_random_count = 50*4;
        m_byte_array_seq.max_random_count = 70*4;

        m_logic_vector_seq = meta_sequence #(META_WIDTH, CHANNELS)::type_id::create("m_logic_vector_seq");
    endtask

    task body();
        m_byte_array_seq.randomize();
        m_logic_vector_seq.randomize();

        fork
            m_byte_array_seq.start(p_sequencer.m_data);
            m_logic_vector_seq.start(p_sequencer.m_meta);
        join_any
    endtask
endclass

