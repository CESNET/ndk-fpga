//-- sequence.sv: AVST sequence
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// This low level sequence define bus functionality
virtual class sequence_simple_rx_base #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned ITEM_WIDTH,
    int unsigned META_WIDTH,
    int unsigned READY_LATENCY
) extends uvm_common::sequence_base
    #(config_sequence, uvm_avst::sequence_item #(REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH));
    `ndk_object_param_utils(uvm_logic_vector_array_avst::sequence_simple_rx_base
                                #(REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY),
                            $sformatf("uvm_logic_vector_array_avst::sequence_simple_rx_base #(%0d,%0d,%0d,%0d,%0d)",
                                      REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY)
    )
    `uvm_declare_p_sequencer(uvm_avst::sequencer#(REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH));

    int unsigned space_size = 0;
    int unsigned data_index;
    uvm_logic_vector_array_avst::data_reg simple_reg;

    uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)                                  data;
    uvm_logic_vector::sequence_item #(META_WIDTH)                                       meta;
    uvm_avst::sequence_item #(REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH) gen;

    typedef enum {state_last, state_next, state_reset, state_overflow, state_latency} state_t;

    sequencer_rx #(ITEM_WIDTH, META_WIDTH)                                              hl_sqr;

    typedef enum {
        state_packet_none,
        state_packet_new,
        state_packet_data,
        state_packet_space,
        state_packet_space_new
    } state_packet_t;
    state_packet_t state_packet;

    rand int unsigned hl_transactions;
    int unsigned hl_transactions_min = 10;
    int unsigned hl_transactions_max = 200;

    constraint c_hl_transations {
        hl_transactions inside {[hl_transactions_min:hl_transactions_max]};
    }

    function new(string name = "sequence_simple_rx_base");
        super.new(name);
    endfunction

    pure virtual task create_sequence_item();

    task send_empty_frame();
        start_item(req);
        req.randomize();
        req.valid = '0;
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
                    hl_sqr.m_meta.get_next_item(meta);
                end

                if (data.data.size() == 0) begin
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
            gen.valid = '0;
            state_packet = state_packet_space_new;
            get_response(rsp);

            simple_reg.latency_cnt = READY_LATENCY;
        end else begin
            // get next item
            create_sequence_item();

            //GET response
            get_response(rsp);

            // Solution of Ready Latency
            if (rsp.ready == 0 && req.valid != 0) begin
                simple_reg.latency_cnt++;
                if (simple_reg.latency_cnt >= READY_LATENCY) begin
                    do begin
                        if (READY_LATENCY == 0) begin
                            start_item(req);
                            finish_item(req);
                        end else begin
                            send_empty_frame();
                        end
                        get_response(rsp);
                    end while (rsp.ready != 1);
                    //assert(std::randomize(simple_reg.latency_cnt) with {simple_reg.latency_cnt inside {[0 : (READY_LATENCY - 1)]}; }) else `uvm_fatal(this.get_full_name(), "\n\tCannot randomize latency");
                    //for (int unsigned it = 0; it < simple_reg.latency_cnt; it++) begin
                    //    send_empty_frame();
                    //    get_response(rsp);
                    //end
                    simple_reg.latency_cnt = 0;
                end
            end else if(rsp.ready == 1) begin
                simple_reg.latency_cnt = 0;
            end

        end

        //SEND FRAME
        start_item(req);
        req.copy(gen);
        finish_item(req);
    endtask

    task body;
        if(!uvm_config_db#(sequencer_rx #(ITEM_WIDTH, META_WIDTH))::get(p_sequencer, "" , "hl_sqr", hl_sqr)) begin
            `uvm_fatal(p_sequencer.get_full_name(), "\n\tsequence sequence_simple_rx cannot get hl_sqr");
        end

        if (!uvm_config_db #(uvm_logic_vector_array_avst::data_reg)::get(
                p_sequencer, "", "simple_reg", simple_reg
            )) begin
            simple_reg = new();
            uvm_config_db #(uvm_logic_vector_array_avst::data_reg)::set(p_sequencer, "", "simple_reg", simple_reg);
        end

        data = null;
        meta = null;
        space_size = 0;
        state_packet = state_packet_space_new;

        req = uvm_avst::sequence_item #(REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH)::type_id::create("req");
        gen = uvm_avst::sequence_item #(REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH)::type_id::create("gen");

        //send empty frame to get first response
        send_empty_frame();
        //when reset on start then wait
        req.valid = '0;
        gen.valid = '0;

        while (hl_transactions > 0 || data != null || |gen.valid) begin
            send_frame();
        end
        //Get last response
        get_response(rsp);
    endtask
endclass

class sequence_simple_rx #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned ITEM_WIDTH,
    int unsigned META_WIDTH,
    int unsigned READY_LATENCY
) extends sequence_simple_rx_base #(REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY);
    `ndk_object_param_utils(
        uvm_logic_vector_array_avst::sequence_simple_rx#(REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY),
        $sformatf("uvm_logic_vector_array_avst::sequence_simple_rx #(%0d,%0d,%0d,%0d,%0d)", REGIONS, REGION_SIZE,
                  ITEM_WIDTH, META_WIDTH, READY_LATENCY)
    )
    uvm_common::rand_length   rand_space_size; //burst set to 0

    //cfg.space_size
    //cfg.rdy_probability_max

    //local int unsigned space_size;
    local int unsigned space_size_dist; //distace betwen minimal and maximal space size
    rand int unsigned space_size_min;
    rand int unsigned space_size_max;

    local int unsigned rdy_probability_dist; //distace betwen minimal and maximal rdy_probability
    rand int unsigned rdy_probability;

    constraint c_space_size {
        space_size_min <= space_size_max;
        space_size_min dist
                {
                    cfg.space_size_min :/ 20,
                    [cfg.space_size_min                    :cfg.space_size_min+space_size_dist/4*1] :/ 30,
                    [cfg.space_size_min+space_size_dist/8*1:cfg.space_size_min+space_size_dist/8*2] :/ 14,
                    [cfg.space_size_min+space_size_dist/8*2:cfg.space_size_min+space_size_dist/8*3] :/ 6,
                    [cfg.space_size_min+space_size_dist/8*3:cfg.space_size_min+space_size_dist/8*4] :/ 3,
                    [cfg.space_size_min+space_size_dist/8*4:cfg.space_size_min+space_size_dist/8*5] :/ 1,
                    [cfg.space_size_min+space_size_dist/8*5:cfg.space_size_min+space_size_dist/8*6] :/ 2,
                    [cfg.space_size_min+space_size_dist/8*6:cfg.space_size_min+space_size_dist/8*7] :/ 3,
                    [cfg.space_size_min+space_size_dist/8*7:cfg.space_size_max] :/ 5,
                    cfg.space_size_max :/ 7
                };

        space_size_max dist
                {
                     cfg.space_size_min :/ 20,
                    [cfg.space_size_min                    :cfg.space_size_min+space_size_dist/4*1] :/ 30,
                    [cfg.space_size_min+space_size_dist/8*1:cfg.space_size_min+space_size_dist/8*2] :/ 14,
                    [cfg.space_size_min+space_size_dist/8*2:cfg.space_size_min+space_size_dist/8*3] :/ 6,
                    [cfg.space_size_min+space_size_dist/8*3:cfg.space_size_min+space_size_dist/8*4] :/ 3,
                    [cfg.space_size_min+space_size_dist/8*4:cfg.space_size_min+space_size_dist/8*5] :/ 1,
                    [cfg.space_size_min+space_size_dist/8*5:cfg.space_size_min+space_size_dist/8*6] :/ 2,
                    [cfg.space_size_min+space_size_dist/8*6:cfg.space_size_min+space_size_dist/8*7] :/ 3,
                    [cfg.space_size_min+space_size_dist/8*7:cfg.space_size_max] :/ 5,
                     cfg.space_size_max :/ 7
                };
    }


    constraint c_probability {
        rdy_probability != 0;
        rdy_probability dist
                {
            [cfg.rdy_probability_min                         :cfg.rdy_probability_min+rdy_probability_dist/4*1] :/ 5,
            [cfg.rdy_probability_min+rdy_probability_dist/8*1:cfg.rdy_probability_min+rdy_probability_dist/8*2] :/ 2,
            [cfg.rdy_probability_min+rdy_probability_dist/8*2:cfg.rdy_probability_min+rdy_probability_dist/8*3] :/ 1,
            [cfg.rdy_probability_min+rdy_probability_dist/8*3:cfg.rdy_probability_min+rdy_probability_dist/8*4] :/ 1,
            [cfg.rdy_probability_min+rdy_probability_dist/8*4:cfg.rdy_probability_min+rdy_probability_dist/8*5] :/ 2,
            [cfg.rdy_probability_min+rdy_probability_dist/8*5:cfg.rdy_probability_min+rdy_probability_dist/8*6] :/ 5,
            [cfg.rdy_probability_min+rdy_probability_dist/8*6:cfg.rdy_probability_min+rdy_probability_dist/8*7] :/ 15,
                    [cfg.rdy_probability_min+rdy_probability_dist/8*7:cfg.rdy_probability_max] :/ 25,
                     cfg.rdy_probability_max :/ 10
                };
    }

    function new (string name = "sequence_simple_rx");
        uvm_common::rand_length_rand  bound_burst;
        uvm_common::rand_length_rand  bound_space_size;

        super.new(name);

        bound_space_size = new();
        bound_space_size.bound_set(100, 700);
        rand_space_size = bound_space_size; //uvm_common::rand_length_rand::new(rand_bound_space);
    endfunction

    /////////
    // CREATE uvm_intel_mac_seg::Sequence_item
    virtual task create_sequence_item();
        int unsigned rdy;
        gen.randomize();

        // TODO: This code need revision.
        // It have to generate  mutch more combination. For example if it is allowed
        // space in packet valid = 101, sof = 100, eof 001.  And sof in last invalid region.
        gen.valid = '0;

        // TODO: Do something with RDY probability
        rdy = $urandom_range(0, 100 - (rdy_probability < 99 ? rdy_probability : 99));
        if (rdy == 0) begin
            // When there is no change to download HL_level transaction then (this is stop sequence)
            // decrement number of generated hl_level_transaction to prevent deadlock.
            if (rdy_probability == 0 && hl_transactions != 0) begin
                hl_transactions--;
            end
            return;
        end

        //TODO: And sof in last invalid region.
        gen.sop   = '0;
        gen.eop   = '0;

        for (int unsigned it = 0; it < REGIONS; it++) begin
             if (state_packet == state_packet_space_new) begin
                 space_size   = $urandom_range(space_size_min, space_size_max);
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
                 bit st_new;
                 bit st_eof;
                 // Check if packet can size in and if straddling is set then put data
                 // on first or when previous packet end in previous region

                 // if straddling is enabled then previous packet have to end in previous region
                 // to start new packet in on first region.
                 if (it > 0 && ((gen.eop[it-1] == 1'b0 && cfg.straddling == 1) || cfg.straddling == 0)) begin
                     st_new = 0;
                 end else begin
                    st_new = 1;
                 end

                 // Check if packet can be put in actual region.
                 if (gen.sop[it] == 0 && st_new == 1 && gen.eop[it] == 0) begin
                    gen.sop[it]     = 1'b1;
                    if (hl_sqr.meta_behav == config_item::META_SOF && META_WIDTH != 0) begin
                        gen.meta[it] = meta.data;
                    end
                    state_packet = state_packet_data;
                 end
             end


             if (state_packet == state_packet_data) begin
                int unsigned loop_end = REGION_SIZE < (data.data.size() - data_index) ?
                    REGION_SIZE : (data.data.size() - data_index);
                 gen.valid[it] = 1;

                 for (int unsigned jt = 0; jt < loop_end; jt++) begin
                      gen.data[it][(jt+1)*ITEM_WIDTH-1 -: ITEM_WIDTH] = data.data[data_index];
                      data_index++;
                 end

                 if (data.data.size() <= data_index) begin
                     if (hl_sqr.meta_behav == config_item::META_EOF && META_WIDTH != 0) begin
                         gen.meta[it] = meta.data;
                     end
                     gen.eop[it]     = 1'b1;
                     gen.empty[it] = REGION_SIZE - loop_end;
                     item_done();
                     state_packet = state_packet_space_new;
                 end
             end
        end
    endtask

    task body;
        space_size_dist = cfg.space_size_max - cfg.space_size_min;
        rdy_probability_dist = cfg.rdy_probability_max - cfg.rdy_probability_min;
        super.body();
    endtask

endclass


class sequence_burst_pcie_rx #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned ITEM_WIDTH,
    int unsigned META_WIDTH,
    int unsigned READY_LATENCY
) extends sequence_simple_rx_base #(REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY);
    `ndk_object_param_utils(uvm_logic_vector_array_avst::sequence_burst_pcie_rx
                                #(REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY),
                            $sformatf("uvm_logic_vector_array_avst::sequence_burst_pcie_rx #(%0d,%0d,%0d,%0d,%0d)",
                                      REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY)
    )
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

    function new (string name = "sequence_burst_pcie_rx");
        uvm_common::rand_length_rand  bound_burst;
        uvm_common::rand_length_rand  bound_space_size;

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

        gen.valid = '0;
        gen.sop   = '0;
        gen.eop   = '0;

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
                    // Check SOP and EOP
                    if (gen.sop[it] == 1 || (gen.eop[it] == 1'b1)) begin
                        break;
                    end

                    // Break when straddling is enable and previous eof is
                    // not set
                    if (it > 0 && ((gen.eop[it-1] == 1'b0 && cfg.straddling == 1) || cfg.straddling == 0)) begin
                        break;
                    end

                    gen.sop[it]     = 1'b1;
                    if (hl_sqr.meta_behav == config_item::META_SOF && META_WIDTH != 0) begin
                        gen.meta[it] = meta.data;
                    end
                    state_packet = state_packet_data;
                end

                if (state_packet == state_packet_data) begin
                    int unsigned loop_end = REGION_SIZE < (data.data.size() - data_index) ?
                        REGION_SIZE : (data.data.size() - data_index);
                    gen.valid[it] = 1;

                    for (int unsigned jt = 0; jt < loop_end; jt++) begin
                        gen.data[it][(jt+1)*ITEM_WIDTH-1 -: ITEM_WIDTH] = data.data[data_index];
                        data_index++;
                    end

                    // End of packet
                    if (data.data.size() <= data_index) begin
                        if (hl_sqr.meta_behav == config_item::META_EOF && META_WIDTH != 0) begin
                            gen.meta[it] = meta.data;
                        end
                        gen.eop[it]     = 1'b1;
                        gen.empty[it] = ~(loop_end-1);
                        item_done();
                        state_packet = state_packet_space_new;
                    end
                end
            end
        end
    endtask

    task body;
        const int unsigned coeficient = REGION_SIZE; //This is just some magic number. which modified length of burst.
        int unsigned probability_min;
        int unsigned probability_max;

        // verilog_lint: waive line-length
        probability_min = cfg.rdy_probability_min + ((cfg.rdy_probability_max - cfg.rdy_probability_min)*rdy_probability_min)/100;
        // verilog_lint: waive line-length
        probability_max = cfg.rdy_probability_min + ((cfg.rdy_probability_max - cfg.rdy_probability_min)*rdy_probability_max)/100;

        rand_burst_size.bound_set(probability_min*coeficient, probability_max*coeficient);
        rand_space_size.bound_set((100 - probability_max) *coeficient,  (100 - probability_min) *coeficient);

        super.body();
    endtask
endclass

class sequence_full_speed_pcie_rx #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned ITEM_WIDTH,
    int unsigned META_WIDTH,
    int unsigned READY_LATENCY
) extends sequence_simple_rx_base #(REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY);
    `ndk_object_param_utils(uvm_logic_vector_array_avst::sequence_full_speed_pcie_rx
                                #(REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY),
                            $sformatf("uvm_logic_vector_array_avst::sequence_full_speed_pcie_rx #(%0d,%0d,%0d,%0d,%0d)",
                                      REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY)
    )

    function new (string name = "sequence_full_speed_pcie_rx");
        super.new(name);
    endfunction

    /////////
    // CREATE uvm_intel_mac_seg::Sequence_item
    virtual task create_sequence_item();
        int unsigned index = 0;
        gen.randomize();

        gen.valid = '0;
        gen.sop   = '0;
        gen.eop   = '0;
        for (int unsigned it = 0; it < REGIONS; it++) begin
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
                // Check SOP and EOP
                if (gen.sop[it] == 1 || (gen.eop[it] == 1'b1)) begin
                    break;
                end

                // Break when straddling is enable and previous eof is
                // not set
                if (it > 0 && ((gen.eop[it-1] == 1'b0 && cfg.straddling == 1) || cfg.straddling == 0)) begin
                    break;
                end

                gen.sop[it]     = 1'b1;
                if (hl_sqr.meta_behav ==  config_item::META_SOF && META_WIDTH != 0) begin
                    gen.meta[it] = meta.data;
                end
                state_packet = state_packet_data;
            end

            if (state_packet == state_packet_data) begin
                int unsigned loop_end = REGION_SIZE < (data.data.size() - data_index) ?
                    REGION_SIZE : (data.data.size() - data_index);
                gen.valid[it] = 1;

                for (int unsigned jt = 0; jt < (loop_end); jt++) begin
                    gen.data[it][(jt+1)*ITEM_WIDTH-1 -: ITEM_WIDTH] = data.data[data_index];
                    data_index++;
                end

                // End of packet
                if (data.data.size() <= data_index) begin
                    if (hl_sqr.meta_behav ==  config_item::META_EOF && META_WIDTH != 0) begin
                        gen.meta[it] = meta.data;
                    end
                    gen.eop[it]     = 1'b1;
                    gen.empty[it] = ~(loop_end-1);
                    item_done();
                    state_packet = state_packet_space_new;
                end
            end
        end
    endtask

endclass

// This is only a slight modification of the sequence_full_speed_rx class where no gaps inside frame are inserted.
// But there are abitrary long gaps getween frames.
class seqv_no_inframe_gap_rx #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned ITEM_WIDTH,
    int unsigned META_WIDTH,
    int unsigned READY_LATENCY
) extends sequence_simple_rx_base #(REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY);
    `ndk_object_param_utils(uvm_logic_vector_array_avst::seqv_no_inframe_gap_rx
                                #(REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY),
                            $sformatf("uvm_logic_vector_array_avst::seqv_no_inframe_gap_rx #(%0d,%0d,%0d,%0d,%0d)",
                                      REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY)
    )

    uvm_common::rand_length   rdy_length;
    uvm_common::rand_rdy      rdy_rdy;

    function new (string name = "seqv_no_inframe_gap_rx");
        super.new(name);
        rdy_rdy    = uvm_common::rand_rdy_rand::new();
        rdy_length = uvm_common::rand_length_rand::new();
    endfunction

    /////////
    // CREATE uvm_intel_mac_seg::Sequence_item
    virtual task create_sequence_item();
        gen.randomize();

        gen.valid = '0;
        gen.sop   = '0;
        gen.eop   = '0;
        for (int unsigned it = 0; it < REGIONS; it++) begin
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
                try_get();
            end

            if (state_packet == state_packet_new) begin
                // Check SOP and EOP position
                if (gen.sop[it] == 1 || (gen.eop[it] == 1'b1)) begin
                    break;
                end

                // Break when straddling is enable and previous eof is
                // not set
                if (it > 0 && ((gen.eop[it-1] == 1'b0 && cfg.straddling == 1) || cfg.straddling == 0)) begin
                    break;
                end

                gen.sop[it]     = 1'b1;
                if (hl_sqr.meta_behav ==  config_item::META_SOF && META_WIDTH != 0) begin
                    gen.meta[it] = meta.data;
                end
                state_packet = state_packet_data;
            end

            if (state_packet == state_packet_data) begin
                int unsigned loop_end = REGION_SIZE < (data.data.size() - data_index) ?
                    REGION_SIZE : (data.data.size() - data_index);
                gen.valid[it] = 1;

                for (int unsigned jt = 0; jt < (loop_end); jt++) begin
                    gen.data[it][(jt+1)*ITEM_WIDTH-1 -: ITEM_WIDTH] = data.data[data_index];
                    data_index++;
                end

                // End of packet
                if (data.data.size() <= data_index) begin
                    if (hl_sqr.meta_behav ==  config_item::META_EOF && META_WIDTH != 0) begin
                        gen.meta[it] = meta.data;
                    end
                    gen.eop[it]     = 1'b1;
                    gen.empty[it] = ~(loop_end-1);
                    item_done();
                    state_packet = state_packet_space_new;
                end
            end
        end
    endtask

    task body;
        rdy_length.bound_set(cfg.space_size_min, cfg.space_size_max);
        rdy_rdy.bound_set(cfg.rdy_probability_min, cfg.rdy_probability_max);

        super.body();
    endtask
endclass

class sequence_stop_pcie_rx #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned ITEM_WIDTH,
    int unsigned META_WIDTH,
    int unsigned READY_LATENCY
) extends sequence_simple_rx_base #(REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY);
    `ndk_object_param_utils(
        uvm_logic_vector_array_avst::sequence_stop_pcie_rx#(
            REGIONS,
            REGION_SIZE,
            ITEM_WIDTH,
            META_WIDTH,
            READY_LATENCY
        ),
        $sformatf("uvm_logic_vector_array_avst::sequence_stop_pcie_rx #(%0d,%0d,%0d,%0d,%0d)", REGIONS, REGION_SIZE,
                  ITEM_WIDTH, META_WIDTH, READY_LATENCY)
    )

    int unsigned hl_transactions_step;

    constraint c_hl_transations_stop {
        hl_transactions dist {[hl_transactions_min:(hl_transactions_min + hl_transactions_step)] :/ 60,
            [(hl_transactions_min+hl_transactions_step)  :(hl_transactions_max - hl_transactions_step)] :/ 30,
                              [(hl_transactions_max - hl_transactions_step):hl_transactions_max] :/10};
    }

    function new (string name = "sequence_stop_pcie_rx");
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

        gen.valid = 0;
        gen.sop   = '0;
        gen.eop   = '0;

        if (hl_transactions != 0) begin
            hl_transactions--;
        end
    endtask
endclass


/////////////////////////////////////////////////////////////////////////
// SEQUENCE LIBRARY RX

class sequence_lib_rx #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned ITEM_WIDTH,
    int unsigned META_WIDTH,
    int unsigned READY_LATENCY
) extends uvm_common::sequence_library
    #(config_sequence, uvm_avst::sequence_item #(REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH));
  `ndk_object_param_utils(
        uvm_logic_vector_array_avst::sequence_lib_rx#(REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY),
        $sformatf("uvm_logic_vector_array_avst::sequence_lib_rx #(%0d,%0d,%0d,%0d,%0d)", REGIONS, REGION_SIZE,
                  ITEM_WIDTH, META_WIDTH, READY_LATENCY)
    )
    `uvm_sequence_library_utils(
        uvm_logic_vector_array_avst::sequence_lib_rx #(REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY))

  function new(string name = "sequence_lib_rx");
    super.new(name);
    init_sequence_library();
  endfunction

    // subclass can redefine and change run sequences
    // can be useful in specific tests
    virtual function void init_sequence(config_sequence param_cfg = null);
        uvm_common::sequence_library::init_sequence(param_cfg);
        this.add_sequence(
            uvm_logic_vector_array_avst::sequence_simple_rx
                #(REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY)::get_type());
        this.add_sequence(
            uvm_logic_vector_array_avst::sequence_full_speed_pcie_rx
                #(REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY)::get_type());
        this.add_sequence(
            uvm_logic_vector_array_avst::seqv_no_inframe_gap_rx
                #(REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY)::get_type());
        this.add_sequence(
            uvm_logic_vector_array_avst::sequence_stop_pcie_rx
                #(REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY)::get_type());
        this.add_sequence(
            uvm_logic_vector_array_avst::sequence_burst_pcie_rx
                #(REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY)::get_type());
    endfunction
endclass

class sequence_lib_rx_speed #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned ITEM_WIDTH,
    int unsigned META_WIDTH,
    int unsigned READY_LATENCY
) extends sequence_lib_rx #(REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY);
    `uvm_object_param_utils(
        uvm_logic_vector_array_avst::sequence_lib_rx_speed #(
            REGIONS,
            REGION_SIZE,
            ITEM_WIDTH,
            META_WIDTH,
            READY_LATENCY
        ))
    `uvm_sequence_library_utils(
        uvm_logic_vector_array_avst::sequence_lib_rx_speed #(
            REGIONS,
            REGION_SIZE,
            ITEM_WIDTH,
            META_WIDTH,
            READY_LATENCY
        ))

  function new(string name = "sequence_lib_rx_speed");
    super.new(name);
    init_sequence_library();
  endfunction

    // subclass can redefine and change run sequences
    // can be useful in specific tests
    virtual function void init_sequence(config_sequence param_cfg = null);
        uvm_common::sequence_library::init_sequence(param_cfg);
        this.add_sequence(
            uvm_logic_vector_array_avst::sequence_full_speed_pcie_rx
                #(REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH, READY_LATENCY)::get_type());
    endfunction
endclass
