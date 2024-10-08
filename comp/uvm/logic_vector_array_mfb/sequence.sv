//-- sequence.sv: Mfb sequence
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet>

//-- SPDX-License-Identifier: BSD-3-Clause



// This low level sequence define bus functionality
class sequence_simple_rx_base #(int unsigned REGIONS, int unsigned REGION_SIZE, int unsigned BLOCK_SIZE, int unsigned ITEM_WIDTH, int unsigned META_WIDTH) extends uvm_common::sequence_base#(config_sequence, uvm_mfb::sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH));
    `uvm_object_param_utils(uvm_logic_vector_array_mfb::sequence_simple_rx_base#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))
    `uvm_declare_p_sequencer(uvm_mfb::sequencer#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH));

    int unsigned space_size = 0;
    int unsigned                              data_index;
    uvm_logic_vector_array::sequence_item#(ITEM_WIDTH) data;
    uvm_logic_vector::sequence_item #(META_WIDTH)      meta;
    sequencer_rx #(ITEM_WIDTH, META_WIDTH)                                           hl_sqr;
    uvm_mfb::sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)  gen;
    typedef enum {state_last, state_next, state_reset} state_t;
    state_t state;

    typedef enum {state_packet_none, state_packet_new, state_packet_data, state_packet_space, state_packet_space_new} state_packet_t;
    state_packet_t state_packet;

    rand int unsigned hl_transactions;
    int unsigned hl_transactions_min = 10;
    int unsigned hl_transactions_max = 100;

    constraint c_hl_transations {
        hl_transactions inside {[hl_transactions_min:hl_transactions_max]};
    }

    function new(string name = "sequence_simple_rx_base");
        super.new(name);
    endfunction

    virtual task create_sequence_item();
    endtask

    task send_empty_frame();
        start_item(req);
        req.randomize();
        req.src_rdy = 0;
        finish_item(req);
    endtask

    function void item_done();
        hl_sqr.m_data.item_done();
        if (hl_sqr.meta_behav != config_item::META_NONE && META_WIDTH != 0) begin
            hl_sqr.m_meta.item_done();
        end
        data = null;
        meta = null;
    endfunction

    task try_get();
        if (data == null && hl_transactions != 0) begin
            hl_sqr.m_data.try_next_item(data);
            data_index = 0;
            if (data != null) begin
                if (hl_sqr.meta_behav != config_item::META_NONE && META_WIDTH != 0) begin
                    //Send metadata
                    hl_sqr.m_meta.get_next_item(meta);
                    hl_transactions--;
                    state_packet = state_packet_new;
                end else if (data.data.size() == 0) begin
                    //Donst send anything if there is no metadata and data size is zero
                    item_done();
                    state_packet = state_packet_none;
                end else begin
                    hl_transactions--;
                    state_packet = state_packet_new;
                end
            end else begin
                state_packet = state_packet_none;
            end
        end
    endtask

    task send_frame();
        // If reset then send empty frame
        if (p_sequencer.reset_sync.has_been_reset()) begin
            if (data != null) begin
                item_done();
            end

            gen.randomize();
            gen.src_rdy = 0;
            state_packet = state_packet_space_new;
            state = state_next;
            get_response(rsp);
        end else begin
            // get next item
            if (state == state_next) begin
                create_sequence_item();
            end

            //GET response
            get_response(rsp);
            if (rsp.src_rdy == 1'b1 && rsp.dst_rdy == 1'b0) begin
                state = state_last;
            end else begin
                state = state_next;
            end
        end

        //SEND FRAME
        start_item(req);
        if (state != state_last) begin
            req.copy(gen);
        end
        finish_item(req);
    endtask

    task body;
        if(!uvm_config_db#(sequencer_rx #(ITEM_WIDTH, META_WIDTH))::get(p_sequencer, "" , "hl_sqr", hl_sqr)) begin
            `uvm_fatal(p_sequencer.get_full_name(), "\n\tsequence sequence_simple_rx cannot get hl_sqr");
        end

        data = null;
        meta = null;
        space_size = 0;
        state_packet = state_packet_space_new;

        req = uvm_mfb::sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::type_id::create("req");
        gen = uvm_mfb::sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::type_id::create("reg");

        //send empty frame to get first response
        send_empty_frame();
        //when reset on start then wait
        req.src_rdy = 0;
        gen.src_rdy = 0;
        state = state_next;

        while (hl_transactions > 0 || data != null || state == state_last || gen.src_rdy == 1) begin
            send_frame();
        end
        //Get last response
        get_response(rsp);
    endtask
endclass


class sequence_simple_rx #(int unsigned REGIONS, int unsigned REGION_SIZE, int unsigned BLOCK_SIZE, int unsigned ITEM_WIDTH, int unsigned META_WIDTH) extends sequence_simple_rx_base #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH);
    `uvm_object_param_utils(uvm_logic_vector_array_mfb::sequence_simple_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))
    uvm_common::rand_length   rdy_length;
    uvm_common::rand_rdy      rdy_rdy;

    function new (string name = "sequence_simple_rx");
        super.new(name);
        rdy_length = uvm_common::rand_length_rand::new();
        rdy_rdy    = uvm_common::rand_rdy_rand::new();
    endfunction

    /////////
    // CREATE uvm_intel_mac_seg::Sequence_item
    virtual task create_sequence_item();
        gen.randomize();

        //randomization of rdy
        void'(rdy_rdy.randomize());
        if (rdy_rdy.m_value == 0) begin
            gen.src_rdy = 0;
            return;
        end

        gen.src_rdy = 0;
        gen.sof     = '0;
        gen.eof     = '0;

        for (int unsigned it = 0; it < REGIONS; it++) begin
            int unsigned index = 0;
            while (index < REGION_SIZE) begin
                if (state_packet == state_packet_space_new) begin
                    void'(rdy_length.randomize());
                    space_size = rdy_length.m_value;
                    state_packet = state_packet_space;
                end


                if (state_packet == state_packet_space) begin
                    if (space_size != 0) begin
                        space_size--;
                    end else begin
                        state_packet = state_packet_none;
                    end
                end

                if (state_packet == state_packet_none) begin
                    try_get();
                end

                if (state_packet == state_packet_new) begin
                    // Check SOF and EOF position if we can insert packet into this region
                    if (gen.sof[it] == 1 || (gen.eof[it] == 1'b1 && (REGION_SIZE*BLOCK_SIZE) >= (index*BLOCK_SIZE + data.data.size()))) begin
                        break;
                    end

                    gen.sof[it]     = 1'b1;
                    gen.sof_pos[it] = index;
                    if (hl_sqr.meta_behav == config_item::META_SOF && META_WIDTH != 0) begin
                        gen.meta[it] = meta.data;
                    end
                    state_packet = state_packet_data;
                end

                if (state_packet == state_packet_data) begin
                    int unsigned loop_end   = BLOCK_SIZE < (data.data.size() - data_index) ? BLOCK_SIZE : (data.data.size() - data_index);
                    gen.src_rdy = 1;

                    for (int unsigned jt = index*BLOCK_SIZE; jt < (index*BLOCK_SIZE + loop_end); jt++) begin
                        gen.data[it][(jt+1)*ITEM_WIDTH-1 -: ITEM_WIDTH] = data.data[data_index];
                        data_index++;
                    end

                    // End of packet
                    if (data.data.size() <= data_index) begin
                        if (hl_sqr.meta_behav == config_item::META_EOF && META_WIDTH != 0) begin
                            gen.meta[it] = meta.data;
                        end
                        gen.eof[it]     = 1'b1;
                        gen.eof_pos[it] = index*BLOCK_SIZE + loop_end-1;
                        item_done();
                        state_packet = state_packet_space_new;
                    end
                end

                index++;
            end
        end
    endtask

    task body;
        rdy_length.bound_set(cfg.space_size_min, cfg.space_size_max);
        rdy_rdy.bound_set(cfg.rdy_probability_min, cfg.rdy_probability_max);

        super.body();
    endtask
endclass

class sequence_burst_rx #(int unsigned REGIONS, int unsigned REGION_SIZE, int unsigned BLOCK_SIZE, int unsigned ITEM_WIDTH, int unsigned META_WIDTH) extends sequence_simple_rx_base #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH);
    `uvm_object_param_utils(uvm_logic_vector_array_mfb::sequence_burst_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))
    uvm_common::rand_length   rand_burst_size; //burst set to 1
    uvm_common::rand_length   rand_space_size; //burst set to 0

    rand int unsigned rdy_probability_min;
    rand int unsigned rdy_probability_max;

    constraint c_probability {
        rdy_probability_min dist {[0:29] :/ 10, [30:49] :/ 20, [50:79] :/ 50, [80:99] :/ 20};
        rdy_probability_max dist {[0:29] :/ 5 , [30:49] :/ 15, [50:79] :/ 30, [80:99] :/ 50};
        rdy_probability_min <= rdy_probability_max;
    }


    typedef enum{SPACE, PACKET} fsm_t;
    fsm_t burst_state = SPACE;
    int unsigned size = 0;

    function new (string name = "sequence_burst_rx");
        uvm_common::rand_length_rand  bound_burst;
        uvm_common::rand_length_rand  bound_space_size;
        uvm_common::rand_length_rand  bound_rdy;
        uvm_common::length_bounds rand_bound[3];
        uvm_common::length_bounds rand_bound_burst[3];
        uvm_common::length_bounds rand_bound_space[4];

        super.new(name);

        bound_burst = new();
        bound_burst.bound_set(300, 1000);
        rand_burst_size = bound_burst; //uvm_common::rand_length_rand::new(rand_bound_burst);

        bound_space_size = new();
        bound_space_size.bound_set(100, 700);
        rand_space_size = bound_space_size; //uvm_common::rand_length_rand::new(rand_bound_space);
    endfunction

    /////////
    // CREATE uvm_intel_mac_seg::Sequence_item
    virtual task create_sequence_item();
        gen.randomize();

        gen.src_rdy = 0;
        gen.sof     = '0;
        gen.eof     = '0;


        if (size == 0) begin
            case (burst_state)
                SPACE : begin
                    assert(rand_burst_size.randomize());
                    size = rand_burst_size.m_value;
                    burst_state = PACKET;
                end

                PACKET : begin
                    if (cfg.rdy_probability_min < 100) begin
                        assert(rand_space_size.randomize());
                        size = rand_space_size.m_value;
                        burst_state = SPACE;
                    end else begin
                        assert(rand_burst_size.randomize());
                        size = rand_burst_size.m_value;
                        burst_state = PACKET;
                    end
                end
            endcase
        end else begin
           size--;
        end


        for (int unsigned it = 0; it < REGIONS; it++) begin
            if (burst_state == SPACE) begin
                gen.data[it] = 'x;
            end else if (burst_state == PACKET) begin
                int unsigned index = 0;
                while (index < REGION_SIZE && burst_state == PACKET) begin
                    if (state_packet == state_packet_space_new) begin
                        space_size   = cfg.space_size_min + $urandom_range(0, REGION_SIZE);
                        state_packet = state_packet_space;
                    end


                    if (state_packet == state_packet_space) begin
                        if (space_size != 0) begin
                            space_size--;
                        end else begin
                            state_packet = state_packet_none;
                        end
                    end

                    if (state_packet == state_packet_none) begin
                        try_get();
                    end

                    if (state_packet == state_packet_new) begin
                        // Check SOF and EOF position if we can insert packet into this region
                        if (gen.sof[it] == 1 || (gen.eof[it] == 1'b1 && (REGION_SIZE*BLOCK_SIZE) >= (index*BLOCK_SIZE + data.data.size()))) begin
                            break;
                        end

                        gen.sof[it]     = 1'b1;
                        gen.sof_pos[it] = index;
                        if (hl_sqr.meta_behav == config_item::META_SOF && META_WIDTH != 0) begin
                            gen.meta[it] = meta.data;
                        end
                        state_packet = state_packet_data;
                    end

                    if (state_packet == state_packet_data) begin
                        int unsigned loop_end   = BLOCK_SIZE < (data.data.size() - data_index) ? BLOCK_SIZE : (data.data.size() - data_index);
                        gen.src_rdy = 1;

                        for (int unsigned jt = index*BLOCK_SIZE; jt < (index*BLOCK_SIZE + loop_end); jt++) begin
                            gen.data[it][(jt+1)*ITEM_WIDTH-1 -: ITEM_WIDTH] = data.data[data_index];
                            data_index++;
                        end

                        // End of packet
                        if (data.data.size() <= data_index) begin
                            if (hl_sqr.meta_behav == config_item::META_EOF && META_WIDTH != 0) begin
                                gen.meta[it] = meta.data;
                            end
                            gen.eof[it]     = 1'b1;
                            gen.eof_pos[it] = index*BLOCK_SIZE + loop_end-1;
                            item_done();
                            state_packet = state_packet_space_new;
                        end
                    end
                    index++;
                //while end
                end
            //end if burst_packet == PACKET
            end
        end
    endtask

    task body;
        const int unsigned coeficient = REGION_SIZE; //This is just some magic number. which modified length of burst.
        int unsigned probability_min;
        int unsigned probability_max;

        probability_min = cfg.rdy_probability_min + ((cfg.rdy_probability_max - cfg.rdy_probability_min)*rdy_probability_min)/100;
        probability_max = cfg.rdy_probability_min + ((cfg.rdy_probability_max - cfg.rdy_probability_min)*rdy_probability_max)/100;

        rand_burst_size.bound_set(probability_min*coeficient, probability_max*coeficient);
        rand_space_size.bound_set((100 - probability_max) *coeficient,  (100 - probability_min) *coeficient);

        super.body();
    endtask
endclass


class sequence_position_rx #(int unsigned REGIONS, int unsigned REGION_SIZE, int unsigned BLOCK_SIZE, int unsigned ITEM_WIDTH, int unsigned META_WIDTH) extends sequence_simple_rx_base #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH);
    `uvm_object_param_utils(uvm_logic_vector_array_mfb::sequence_position_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))

    uvm_common::rand_length      rdy_length;
    uvm_common::rand_rdy         rdy_rdy;
    rand logic [REGION_SIZE-1:0] sof_pos;

    constraint sof_pos_c {sof_pos > 0;};

    function new (string name = "sequence_simple_rx");
        super.new(name);
        rdy_length = uvm_common::rand_length_rand::new();
        rdy_rdy    = uvm_common::rand_rdy_rand::new();
    endfunction

    /////////
    // CREATE uvm_intel_mac_seg::Sequence_item
    virtual task create_sequence_item();
        gen.randomize();

        //randomization of rdy
        void'(rdy_rdy.randomize());
        if (rdy_rdy.m_value == 0) begin
            gen.src_rdy = 0;
            return;
        end

        gen.src_rdy = 0;
        gen.sof     = '0;
        gen.eof     = '0;

        for (int unsigned it = 0; it < REGIONS; it++) begin
            int unsigned index = 0;
            while (index < REGION_SIZE) begin
                if (state_packet == state_packet_space_new) begin
                    void'(rdy_length.randomize());
                    space_size   = rdy_length.m_value;
                    state_packet = state_packet_space;
                end


                if (state_packet == state_packet_space) begin
                    if (space_size != 0) begin
                        space_size--;
                    end else begin
                        state_packet = state_packet_none;
                    end
                end

                if (state_packet == state_packet_none) begin
                    if (sof_pos[index] == 1) begin //get next packet only if there is position for sof
                        try_get();
                    end
                end

                if (state_packet == state_packet_new) begin
                    // Check SOF and EOF position if we can insert packet into this region
                    if (gen.sof[it] == 1 || (gen.eof[it] == 1'b1 && (REGION_SIZE*BLOCK_SIZE) >= (index*BLOCK_SIZE + data.data.size()))) begin
                        break;
                    end

                    gen.sof[it]     = 1'b1;
                    gen.sof_pos[it] = index;
                    if (hl_sqr.meta_behav ==  config_item::META_SOF && META_WIDTH != 0) begin
                        gen.meta[it] = meta.data;
                    end
                    state_packet = state_packet_data;
                end

                if (state_packet == state_packet_data) begin
                    int unsigned loop_end   = BLOCK_SIZE < (data.data.size() - data_index) ? BLOCK_SIZE : (data.data.size() - data_index);
                    gen.src_rdy = 1;

                    for (int unsigned jt = index*BLOCK_SIZE; jt < (index*BLOCK_SIZE + loop_end); jt++) begin
                        gen.data[it][(jt+1)*ITEM_WIDTH-1 -: ITEM_WIDTH] = data.data[data_index];
                        data_index++;
                    end

                    // End of packet
                    if (data.data.size() <= data_index) begin
                        if (hl_sqr.meta_behav ==  config_item::META_EOF && META_WIDTH != 0) begin
                            gen.meta[it] = meta.data;
                        end
                        gen.eof[it]     = 1'b1;
                        gen.eof_pos[it] = index*BLOCK_SIZE + loop_end-1;
                        item_done();
                        state_packet = state_packet_space_new;
                    end
                end

                index++;
            end
        end
    endtask

    task body;
        rdy_length.bound_set(cfg.space_size_min, cfg.space_size_max);
        rdy_rdy.bound_set(cfg.rdy_probability_min, cfg.rdy_probability_max);

        super.body();
    endtask
endclass


class sequence_full_speed_rx #(int unsigned REGIONS, int unsigned REGION_SIZE, int unsigned BLOCK_SIZE, int unsigned ITEM_WIDTH, int unsigned META_WIDTH) extends sequence_simple_rx_base #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH);
    `uvm_object_param_utils(uvm_logic_vector_array_mfb::sequence_full_speed_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))

    function new (string name = "sequence_full_speed_rx");
        super.new(name);
    endfunction

    /////////
    // CREATE uvm_intel_mac_seg::Sequence_item
    virtual task create_sequence_item();
        int unsigned index = 0;
        gen.randomize();

        gen.src_rdy = 0;
        gen.sof     = '0;
        gen.eof     = '0;
        for (int unsigned it = 0; it < REGIONS; it++) begin
            int unsigned index = 0;
            while (index < REGION_SIZE) begin
                if (state_packet == state_packet_space_new) begin
                    state_packet = state_packet_space;
                    space_size   = cfg.space_size_min;
                end


                if (state_packet == state_packet_space) begin
                    if (space_size != 0) begin
                        space_size--;
                    end else begin
                        state_packet = state_packet_none;
                    end
                end

                if (state_packet == state_packet_none) begin
                    try_get();
                end

                if (state_packet == state_packet_new) begin
                    // Check SOF and EOF position if we can insert packet into this region
                    if (gen.sof[it] == 1 || (gen.eof[it] == 1'b1 && (REGION_SIZE*BLOCK_SIZE) >= (index*BLOCK_SIZE + data.data.size()))) begin
                        break;
                    end

                    gen.sof[it]     = 1'b1;
                    gen.sof_pos[it] = index;
                    if (hl_sqr.meta_behav ==  config_item::META_SOF && META_WIDTH != 0) begin
                        gen.meta[it] = meta.data;
                    end
                    state_packet = state_packet_data;
                end

                if (state_packet == state_packet_data) begin
                    int unsigned loop_end   = BLOCK_SIZE < (data.data.size() - data_index) ? BLOCK_SIZE : (data.data.size() - data_index);
                    gen.src_rdy = 1;

                    for (int unsigned jt = index*BLOCK_SIZE; jt < (index*BLOCK_SIZE + loop_end); jt++) begin
                        gen.data[it][(jt+1)*ITEM_WIDTH-1 -: ITEM_WIDTH] = data.data[data_index];
                        data_index++;
                    end

                    // End of packet
                    if (data.data.size() <= data_index) begin
                        if (hl_sqr.meta_behav ==  config_item::META_EOF && META_WIDTH != 0) begin
                            gen.meta[it] = meta.data;
                        end
                        gen.eof[it]     = 1'b1;
                        gen.eof_pos[it] = index*BLOCK_SIZE + loop_end-1;
                        item_done();
                        state_packet = state_packet_space_new;
                    end
                end
                index++;
            end
        end
    endtask

endclass

class sequence_stop_rx #(int unsigned REGIONS, int unsigned REGION_SIZE, int unsigned BLOCK_SIZE, int unsigned ITEM_WIDTH, int unsigned META_WIDTH) extends sequence_simple_rx_base #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH);
    `uvm_object_param_utils(uvm_logic_vector_array_mfb::sequence_stop_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))

    int unsigned hl_transactions_step;

    constraint c_hl_transations_stop {
        hl_transactions dist {[hl_transactions_min:(hl_transactions_min + hl_transactions_step)] :/ 60,
                              [(hl_transactions_min+hl_transactions_step)  :(hl_transactions_max - hl_transactions_step)] :/ 30,
                              [(hl_transactions_max - hl_transactions_step):hl_transactions_max] :/10};
    }

    function new (string name = "sequence_stop_rx");
        super.new(name);
        hl_transactions_min = 10;
        hl_transactions_max = 300;

        hl_transactions_step = (hl_transactions_max - hl_transactions_min)/10;
    endfunction

    /////////
    // CREATE uvm_intel_mac_seg::Sequence_item
    virtual task create_sequence_item();
        int unsigned index = 0;
        gen.randomize();

        gen.src_rdy = 0;
        gen.sof     = '0;
        gen.eof     = '0;

        if (hl_transactions != 0) begin
            hl_transactions--;
        end
    endtask
endclass
