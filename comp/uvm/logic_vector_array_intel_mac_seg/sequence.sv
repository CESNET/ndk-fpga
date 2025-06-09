/*
 * file       : sequence.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: convert byte_array to intel seq mac
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

//////////////////////////////////////////////////
// BASE CLASS CONTAINING COMMON FUNCTIONS
virtual class sequence_simple_rx_base #(int unsigned SEGMENTS) extends uvm_intel_mac_seg::sequence_simple_rx #(SEGMENTS);
   `uvm_object_param_utils(uvm_logic_vector_array_intel_mac_seg::sequence_simple_rx_base#(SEGMENTS))
   `uvm_declare_p_sequencer(uvm_intel_mac_seg::sequencer#(SEGMENTS));
   localparam LOGIC_WIDTH = 6;
   localparam ITEM_WIDTH = 8;

    sequencer             hl_sqr;
    uvm_intel_mac_seg::sequence_item #(SEGMENTS) gen;
    //DAta
    uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)  hl_tr = null;
    uvm_logic_vector::sequence_item#(LOGIC_WIDTH)       hl_tr_err = null;
    int unsigned                                        hl_tr_index;

    //////////////////////////////////
    // RANDOMIZATION
    rand int unsigned hl_transactions;
    int unsigned hl_transactions_min = 10;
    int unsigned hl_transactions_max = 200;

    rand int unsigned  ready_delay;
    const int unsigned ready_delay_min = 1;
    const int unsigned ready_delay_max = 8;

    constraint c_hl_transactions{
        hl_transactions inside {[hl_transactions_min:hl_transactions_max]};
    };

    constraint c_valid_delay{
        ready_delay inside {[ready_delay_min:ready_delay_max]};
    };

    //////////////////////////////////
    // FUNCTIONS
    function new (string name = "req");
        super.new(name);
    endfunction

    pure virtual task create_sequence_item();

    task send_empty_frame();
        start_item(req);
        req.randomize();
        req.inframe = '{ SEGMENTS{{0}} };
        finish_item(req);
    endtask

    function void prepare_valid_delay_fifo();
        if (ready_delay < hl_sqr.ready.size()) begin
            for (int unsigned it = hl_sqr.ready.size(); it < ready_delay; it++) begin
                hl_sqr.ready.push_back(1);
            end
        end else begin
            logic rdy_val;

            rdy_val = hl_sqr.ready[$];
            while (hl_sqr.ready.size() > ready_delay) begin
                void'(hl_sqr.ready.pop_front());
                rdy_val &= hl_sqr.ready[$];
            end

            // if there is value 0 somewhere in removed fifo then
            // put on new top value 0. This prevent not fall down
            // valid when ready signal is fall down
            hl_sqr.ready[$] = rdy_val;
        end
    endfunction

    task reset_handle();
        //wait until stop reset
        while (p_sequencer.reset_sync.has_been_reset()) begin
            //SETUP RESET
            if (hl_tr != null) begin
                done();
            end

            send_empty_frame();
            response_process();
        end
    endtask

    task try_get();
        if (hl_tr == null && hl_transactions != 0) begin
            hl_sqr.m_packet.try_next_item(hl_tr);
            hl_tr_index = 0;
            if (hl_tr != null) begin
                hl_transactions--;
                hl_sqr.m_error.get_next_item(hl_tr_err);
            end
        end
    endtask

    task done();
        //clear data
        hl_tr = null;
        hl_sqr.m_packet.item_done();
        hl_sqr.m_error.item_done();
    endtask

    virtual task response_process();
        get_response(rsp);
        hl_sqr.ready.push_back(rsp.ready);
    endtask

    task send_frame();
        // Handle delayed ready
        while (hl_sqr.ready.pop_front() != 1) begin
            start_item(req);
            req.randomize();
            req.valid = 0;
            finish_item(req);
            response_process();
        end
        // Handle reset
        reset_handle();

        // CREATE intel_mac_seg::Sequence_item
        create_sequence_item();

        //GET response
        response_process();

        //SEND FRAME
        start_item(req);
        req.copy(gen);
        finish_item(req);
    endtask


    /////////////////////////////////////////////////////
    // BODY
    task body();
        if(!uvm_config_db#(sequencer)::get(p_sequencer, "" , "hl_sqr", hl_sqr)) begin
            `uvm_fatal(p_sequencer.get_full_name(), "\n\tsequence sequence_simple_rx cannot get hl_sqr");
        end


        hl_tr = null;
        hl_tr_err = null;

        req = uvm_intel_mac_seg::sequence_item #(SEGMENTS)::type_id::create("req");
        gen = uvm_intel_mac_seg::sequence_item #(SEGMENTS)::type_id::create("reg");

        prepare_valid_delay_fifo();


        //send empty frame to get first response
        send_empty_frame();
        while (hl_transactions > 0 || hl_tr != null) begin
            send_frame();
        end

        //Get last response
        response_process();
    endtask

endclass

class sequence_simple_rx #(int unsigned SEGMENTS) extends sequence_simple_rx_base #(SEGMENTS);
    `uvm_object_param_utils(uvm_logic_vector_array_intel_mac_seg::sequence_simple_rx#(SEGMENTS))

    local int unsigned space_size;
    rand int unsigned  space_size_min;
    rand int unsigned  space_size_max;

    constraint c_space_size {
        space_size_min <= space_size_max;
        space_size_min dist { [0*SEGMENTS:1*SEGMENTS] :/ 60,  [1*SEGMENTS:3*SEGMENTS] :/ 10,  [3*SEGMENTS:5*SEGMENTS] :/ 5,
                              [5*SEGMENTS:90*SEGMENTS] :/ 3,  [90*SEGMENTS:95*SEGMENTS] :/ 7, [95*SEGMENTS:100*SEGMENTS] :/ 15};
        space_size_max dist { [0*SEGMENTS:1*SEGMENTS] :/ 60,  [1*SEGMENTS:3*SEGMENTS] :/ 10,  [3*SEGMENTS:5*SEGMENTS] :/ 5,
                              [5*SEGMENTS:90*SEGMENTS] :/ 3,  [90*SEGMENTS:95*SEGMENTS] :/ 7, [95*SEGMENTS:100*SEGMENTS] :/ 15};
    }

    function new (string name = "req");
        super.new(name);
        space_size = 0;
    endfunction

    /////////
    // CREATE intel_mac_seg::Sequence_item
    virtual task create_sequence_item();
        gen.randomize();
        gen.valid = ($urandom_range(0,10) == 0);
        gen.inframe = '{ SEGMENTS{{0}} };
        for (int unsigned it = 0; it < SEGMENTS; it++) begin
            if (hl_tr == null) begin
                if (space_size == 0) begin
                    try_get();
                end else begin
                    space_size--;
                end
            end

            if (hl_tr == null) begin
                gen.inframe[it] = 0;
            end else begin
                gen.valid = 1;
                if ((hl_tr_index + 8) < hl_tr.data.size()) begin
                    for (int unsigned jt = 0; jt < 8; jt++) begin
                        gen.data[it][(jt+1)*8-1 -: 8] = hl_tr.data[hl_tr_index + jt];
                    end
                    //gen.data[it] = {<<byte{hl_tr.data[hl_tr_index +: 8]}};
                    gen.inframe[it] = 1;
                end else begin
                    int unsigned end_size = hl_tr.data.size() - hl_tr_index;
                    for (int unsigned jt = 0; jt < end_size; jt++) begin
                        gen.data[it][(jt+1)*8-1 -: 8] = hl_tr.data[hl_tr_index + jt];
                    end
                    //set output
                    gen.inframe[it]   = 0;
                    gen.eop_empty[it] = 8 - end_size;
                    {>>{gen.fcs_error[it], gen.error[it], gen.status_data[it]}} = hl_tr_err.data;
                    //clear data
                    done();
                    assert(std::randomize(space_size) with { space_size inside {[space_size_min:space_size_max]};}  );
                end
                hl_tr_index += 8;
            end
        end
    endtask
endclass

class sequence_space_same_rx #(int unsigned SEGMENTS) extends sequence_simple_rx_base #(SEGMENTS);
    `uvm_object_param_utils(uvm_logic_vector_array_intel_mac_seg::sequence_space_same_rx#(SEGMENTS))

    rand int unsigned space_size_same;
    local int unsigned space_size;

    constraint c_space_size {
        space_size_same dist { [0*SEGMENTS:1*SEGMENTS] :/ 60,  [1*SEGMENTS:3*SEGMENTS] :/ 10,  [3*SEGMENTS:5*SEGMENTS] :/ 5,
                              [5*SEGMENTS:90*SEGMENTS] :/ 3,  [90*SEGMENTS:95*SEGMENTS] :/ 7, [95*SEGMENTS:100*SEGMENTS] :/ 15};
    }

    function new (string name = "req");
        super.new(name);
    endfunction

    /////////
    // CREATE intel_mac_seg::Sequence_item
    virtual task create_sequence_item();
        gen.randomize();
        gen.valid = ($urandom_range(0,10) == 0);
        gen.inframe = '{ SEGMENTS{{0}} };
        for (int unsigned it = 0; it < SEGMENTS; it++) begin
            if (hl_tr == null) begin
                if (space_size == 0) begin
                    try_get();
                end else begin
                    space_size--;
                end
            end

            if (hl_tr == null) begin
                gen.inframe[it] = 0;
            end else begin
                gen.valid = 1;
                if ((hl_tr_index + 8) < hl_tr.data.size()) begin
                    gen.data[it] = {<<byte{hl_tr.data[hl_tr_index +: 8]}};
                    gen.inframe[it] = 1;
                end else begin
                    int unsigned end_size = hl_tr.data.size() - hl_tr_index;
                    for (int unsigned jt = 0; jt < end_size; jt++) begin
                        gen.data[it][(jt+1)*8-1 -: 8] = hl_tr.data[hl_tr_index + jt];
                    end
                    //set output
                    gen.inframe[it]   = 0;
                    gen.eop_empty[it] = 8 - end_size;
                    {>>{gen.fcs_error[it], gen.error[it], gen.status_data[it]}} = hl_tr_err.data;
                    //clear data
                    done();
                    space_size = space_size_same;
                end
                hl_tr_index += 8;
            end
        end
    endtask
endclass


class sequence_sop_pos_rx #(int unsigned SEGMENTS) extends sequence_simple_rx_base #(SEGMENTS);
    `uvm_object_param_utils(uvm_logic_vector_array_intel_mac_seg::sequence_sop_pos_rx #(SEGMENTS))

    rand logic [SEGMENTS-1:0] sop_position;

    constraint c_sop_position {
        $countones(sop_position) dist {
            0 :/ 3,
            1 :/ 25,
            [1:SEGMENTS/3] :/ 32,
            [SEGMENTS/3:SEGMENTS*2/3] :/ 30,
            [SEGMENTS*2/3:SEGMENTS-1] :/ 10
        };
    };

    function new (string name = "req");
        super.new(name);
    endfunction

    /////////
    // CREATE intel_mac_seg::Sequence_item
    virtual task create_sequence_item();
        gen.randomize();
        gen.valid = ($urandom_range(0,10) == 0);
        gen.inframe = '{ SEGMENTS{{0}} };
        // if this is stop sequence then decrement transactions and return
        if (sop_position == 0) begin
            hl_transactions--;
            return;
        end

        for (int unsigned it = 0; it < SEGMENTS; it++) begin
            if (hl_tr == null &&  sop_position[it] == 1) begin
                try_get();
            end

            if (hl_tr == null) begin
                gen.inframe[it] = 0;
            end else begin
                gen.valid = 1;
                if ((hl_tr_index + 8) < hl_tr.data.size()) begin
                    gen.data[it] = {<<byte{hl_tr.data[hl_tr_index +: 8]}};
                    gen.inframe[it] = 1;
                end else begin
                    int unsigned end_size = hl_tr.data.size() - hl_tr_index;
                    for (int unsigned jt = 0; jt < end_size; jt++) begin
                        gen.data[it][(jt+1)*8-1 -: 8] = hl_tr.data[hl_tr_index + jt];
                    end
                    //set output
                    gen.inframe[it]   = 0;
                    gen.eop_empty[it] = 8 - end_size;
                    {>>{gen.fcs_error[it], gen.error[it], gen.status_data[it]}} = hl_tr_err.data;
                    //clear data
                    done();
                end
                hl_tr_index += 8;
            end
        end
    endtask
endclass


class sequence_max_rx #(int unsigned SEGMENTS) extends sequence_simple_rx_base #(SEGMENTS);
    `uvm_object_param_utils(uvm_logic_vector_array_intel_mac_seg::sequence_max_rx#(SEGMENTS))

    function new (string name = "req");
        super.new(name);
        this.hl_transactions_max = 100;
    endfunction

    function void pre_randomize();
        super.pre_randomize();
    endfunction

    /////////
    // CREATE intel_mac_seg::Sequence_item
    virtual task create_sequence_item();
        gen.randomize();
        gen.valid = ($urandom_range(0,10) != 0);
        gen.inframe = '{ SEGMENTS{{0}} };
        for (int unsigned it = 0; it < SEGMENTS; it++) begin
            try_get();

            if (hl_tr == null) begin
                gen.inframe[it] = 0;
            end else begin
                gen.valid = 1;
                if ((hl_tr_index + 8) < hl_tr.data.size()) begin
                    gen.data[it] = {<<byte{hl_tr.data[hl_tr_index +: 8]}};
                    gen.inframe[it] = 1;
                end else begin
                    int unsigned end_size = hl_tr.data.size() - hl_tr_index;
                    for (int unsigned jt = 0; jt < end_size; jt++) begin
                        gen.data[it][(jt+1)*8-1 -: 8] = hl_tr.data[hl_tr_index + jt];
                    end
                    //set output
                    gen.inframe[it]   = 0;
                    gen.eop_empty[it] = 8 - end_size;
                    {>>{gen.fcs_error[it], gen.error[it], gen.status_data[it]}} = hl_tr_err.data;
                    done();
                end
                hl_tr_index += 8;
            end
        end
    endtask
endclass

//uvm_sequence #();
///////////////////////////////////////////////////////////////
// SEQUENCE LIBRARY
///////////////////////////////////////////////////////////////
class sequence_lib_rx #(int unsigned SEGMENTS) extends uvm_sequence_library#(uvm_intel_mac_seg::sequence_item #(SEGMENTS));
  `uvm_object_param_utils(uvm_logic_vector_array_intel_mac_seg::sequence_lib_rx#(SEGMENTS))
  `uvm_sequence_library_utils(uvm_logic_vector_array_intel_mac_seg::sequence_lib_rx#(SEGMENTS))
  function new(string name = "");
    super.new(name);
    init_sequence_library();
  endfunction
    // subclass can redefine and change run sequences
    // can be useful in specific tests
    virtual function void init_sequence();
        this.add_sequence(uvm_logic_vector_array_intel_mac_seg::sequence_simple_rx#(SEGMENTS)::get_type());
        this.add_sequence(uvm_logic_vector_array_intel_mac_seg::sequence_sop_pos_rx #(SEGMENTS)::get_type());
        this.add_sequence(uvm_logic_vector_array_intel_mac_seg::sequence_space_same_rx #(SEGMENTS)::get_type());
        this.add_sequence(uvm_logic_vector_array_intel_mac_seg::sequence_max_rx#(SEGMENTS)::get_type());
    endfunction
endclass

