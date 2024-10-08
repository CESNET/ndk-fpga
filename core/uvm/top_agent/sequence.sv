//-- sequence.sv: create from packet transaction mfb and mvb transaction 
//-- Copyright (C) 2024 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause 


class sequence_base#(type TR_TYPE) extends uvm_sequence #(TR_TYPE);
    `uvm_object_param_utils(uvm_app_core_top_agent::sequence_base#(TR_TYPE))

    int unsigned transaction_min = 100;
    int unsigned transaction_max = 300;

    rand int unsigned transactions;

    constraint c_transactions {
        transactions inside {[transaction_min:transaction_max]};
    }

    // Constructor - creates new instance of this class
    function new(string name = "sequence");
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

        req = TR_TYPE::type_id::create("req", m_sequencer);

        it = 0;
        while(it < transactions && (state == null || !state.stopped())) begin
            //generat new packet
            start_item(req);
            req.randomize() with {req.data.size() inside {[60:1500]}; }; 
            finish_item(req);

            it++;
        end
    endtask
endclass



class logic_vector_array#(ITEM_WIDTH, META_WIDTH) extends uvm_sequence #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH));
    `uvm_object_param_utils(uvm_app_core_top_agent::logic_vector_array#(ITEM_WIDTH, META_WIDTH))

    uvm_common::fifo#(sequence_item#(ITEM_WIDTH, META_WIDTH)) fifo;
    //mailbox#(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)) packet_export;

    // Constructor - creates new instance of this class
    function new(string name = "sequence");
        super.new(name);
    endfunction

    // -----------------------
    // Functions.
    // -----------------------
    task body;
        req = uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)::type_id::create("req", m_sequencer);
        if(!uvm_config_db#(uvm_common::fifo#(sequence_item#(ITEM_WIDTH, META_WIDTH)))::get(m_sequencer, "", "fifo", fifo)) begin
            `uvm_fatal(m_sequencer.get_full_name(), "\n\tFailed to get packet msg box");
        end

        forever begin
            sequence_item#(ITEM_WIDTH, META_WIDTH) tmp_packet;

            //wait to end reset
            fifo.get(tmp_packet);

            //generat new packet
            start_item(req);
            req.data = tmp_packet.data; 
            finish_item(req);
        end
    endtask
endclass


class logic_vector_sequence #(ITEM_WIDTH, META_WIDTH) extends uvm_sequence #(uvm_logic_vector::sequence_item #(META_WIDTH));
    `uvm_object_param_utils(uvm_app_core_top_agent::logic_vector_sequence #(ITEM_WIDTH, META_WIDTH))

    uvm_common::fifo#(sequence_item#(ITEM_WIDTH, META_WIDTH)) fifo;

    // ------------------------------------------------------------------------
    // Variables
    int unsigned transaction_count_max = 2048;
    int unsigned transaction_count_min = 32;
    rand int unsigned transaction_count;

    constraint tr_cnt_cons {transaction_count inside {[transaction_count_min:transaction_count_max]};}

    // ------------------------------------------------------------------------
    // Constructor
    function new(string name = "logic_vector_sequence_simple_eth");
        super.new(name);
    endfunction

    task body;

        req = uvm_logic_vector::sequence_item#(META_WIDTH)::type_id::create("req", m_sequencer);
        if(!uvm_config_db#(uvm_common::fifo#(sequence_item#(ITEM_WIDTH, META_WIDTH)))::get(m_sequencer, "", "fifo", fifo)) begin
            `uvm_fatal(m_sequencer.get_full_name(), "\n\tFailed to get packet msg box");
        end

        forever begin
            bit bitstream [];
            uvm_app_core_top_agent::sequence_item#(ITEM_WIDTH, META_WIDTH) high_tr;

            //wait to end reset
            fifo.get(high_tr);

            //generat new packet
            start_item(req);
            req.data = high_tr.item2meta();
            //high_tr.pack(bitstream);            
            //req.data = { >> {bitstream}};

            finish_item(req);
        end
    endtask
endclass


