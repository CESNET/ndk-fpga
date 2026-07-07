//-- sequence.sv: Mfb sequence
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet>

//-- SPDX-License-Identifier: BSD-3-Clause



// This low level sequence define bus functionality
class sequence_rx_base #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned BLOCK_SIZE,
    int unsigned ITEM_WIDTH,
    int unsigned META_WIDTH
) extends uvm_common::sequence_base#(config_sequence, uvm_mfb::sequence_item #(
                    REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH
          ));
    `ndk_object_param_utils(
        uvm_logic_vector_array_mfb::sequence_rx_base #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH),
        $sformatf("uvm_logic_vector_array_mfb::sequence_rx_base #(%0d,%0d,%0d,%0d,%0d)", REGIONS, REGION_SIZE,
                  BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)
    )
    `uvm_declare_p_sequencer(uvm_mfb::sequencer#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH));

    int unsigned space_size = 0;
    int unsigned                              data_index;
    uvm_logic_vector_array::sequence_item#(ITEM_WIDTH) data;
    uvm_logic_vector::sequence_item #(META_WIDTH)      meta;
    sequencer_rx #(ITEM_WIDTH, META_WIDTH)                                           hl_sqr;
    uvm_mfb::sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)  gen;
    typedef enum {state_last, state_next, state_reset} state_t;
    state_t state;

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
    int unsigned hl_transactions_max = 300;

    constraint c_hl_transations {
        hl_transactions inside {[hl_transactions_min:hl_transactions_max]};
    }

    function new(string name = "sequence_rx_base");
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

    function void tr_init(ref uvm_mfb::sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) tr);
        case (cfg.generate_invalid)
            config_sequence::INVALID_ZERO  :
                begin
                    for (int unsigned it = 0; it < REGIONS; it++) begin
                        tr.data[it]    = '0;
                        tr.meta[it]    = '0;
                        tr.sof_pos[it] = '0;
                        tr.eof_pos[it] = '0;
                    end
                    tr.sof     = '0;
                    tr.eof     = '0;
                    tr.src_rdy = 0;
                end
            config_sequence::INVALID_UNDEF :
                begin
                    for (int unsigned it = 0; it < REGIONS; it++) begin
                        tr.data[it]    = 'x;
                        tr.meta[it]    = 'x;
                        tr.sof_pos[it] = 'x;
                        tr.eof_pos[it] = 'x;
                    end
                    tr.sof     = 'x;
                    tr.eof     = 'x;
                    tr.src_rdy = 0;
                end
            config_sequence::INVALID_RAND  :
                assert(tr.randomize() with {tr.src_rdy == 0;});
        endcase
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
            `uvm_fatal(p_sequencer.get_full_name(), "\n\tsequence sequence_rx_simple cannot get hl_sqr");
        end

        data = null;
        meta = null;
        space_size = 0;
        state_packet = state_packet_space_new;

        req = uvm_mfb::sequence_item #(
                REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH
        )::type_id::create("req");
        gen = uvm_mfb::sequence_item #(
                REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH
        )::type_id::create("gen");

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


class sequence_rx_simple #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned BLOCK_SIZE,
    int unsigned ITEM_WIDTH,
    int unsigned META_WIDTH
) extends sequence_rx_base #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH);
    `ndk_object_param_utils(
        uvm_logic_vector_array_mfb::sequence_rx_simple#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH),
        $sformatf("uvm_logic_vector_array_mfb::sequence_rx_simple #(%0d,%0d,%0d,%0d,%0d)", REGIONS, REGION_SIZE,
                  BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)
    )

    rand int unsigned space_size_min;
    rand int unsigned space_size_max;

    constraint c_space_size {
        space_size_min <= space_size_max;
        space_size_min dist {
             cfg.space_size_min :/ 5,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*0 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*1] :/ 20,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*1 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*2] :/ 7,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*2 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*3] :/ 5,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*3 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*4] :/ 3,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*4 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*5] :/ 2,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*5 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*6] :/ 1,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*6 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*7] :/ 1,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*7 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*8] :/ 3,
             cfg.space_size_max :/ 5
        };

        space_size_max dist {
             cfg.space_size_min :/ 5,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*0 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*1] :/ 20,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*1 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*2] :/ 7,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*2 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*3] :/ 5,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*3 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*4] :/ 3,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*4 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*5] :/ 2,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*5 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*6] :/ 1,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*6 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*7] :/ 1,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*7 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*8] :/ 3,
             cfg.space_size_max :/ 5
        };
    }

    rand int unsigned rdy_probability;

    constraint c_rdy_probability {
        rdy_probability != 0;
        rdy_probability dist {
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*0 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*1] :/ 3,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*1 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*2] :/ 1,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*2 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*3] :/ 1,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*3 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*4] :/ 1,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*4 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*5] :/ 3,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*5 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*6] :/ 5,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*6 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*7] :/ 10,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*7 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*8] :/ 20,
             cfg.rdy_probability_max :/ 30
        };
    }

    function new (string name = "sequence_rx_simple");
        super.new(name);
    endfunction

    /////////
    // CREATE uvm_intel_mac_seg::Sequence_item
    virtual task create_sequence_item();
        int unsigned rdy;
        logic src_rdy;
        logic [REGIONS-1 : 0] sof;
        logic [REGIONS-1 : 0] eof;

        tr_init(gen);
        src_rdy = 0;
        sof     = '0;
        eof     = '0;

        assert(std::randomize(rdy) with { rdy dist {0 :/ (100 -rdy_probability), 1 :/ rdy_probability}; } );
        if (rdy == 0) begin
            return;
        end


        for (int unsigned it = 0; it < REGIONS; it++) begin
            int unsigned index = 0;
            while (index < REGION_SIZE) begin
                if (state_packet == state_packet_space_new) begin
                    space_size = $urandom_range(space_size_min, space_size_max);
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
                    if (sof[it] == 1 ||
                            (eof[it] == 1'b1 && (REGION_SIZE*BLOCK_SIZE) >= (index*BLOCK_SIZE + data.data.size()))
                    ) begin
                        break;
                    end

                    sof[it]     = 1'b1;
                    gen.sof_pos[it] = index;
                    if (hl_sqr.meta_behav == config_item::META_SOF && META_WIDTH != 0) begin
                        gen.meta[it] = meta.data;
                    end
                    state_packet = state_packet_data;
                end

                if (state_packet == state_packet_data) begin
                    const int unsigned data_rest = (data.data.size() - data_index);
                    const int unsigned loop_end = BLOCK_SIZE < data_rest ? BLOCK_SIZE : data_rest;
                    src_rdy = 1;

                    for (int unsigned jt = index*BLOCK_SIZE; jt < (index*BLOCK_SIZE + loop_end); jt++) begin
                        gen.data[it][(jt+1)*ITEM_WIDTH-1 -: ITEM_WIDTH] = data.data[data_index];
                        data_index++;
                    end

                    // End of packet
                    if (data.data.size() <= data_index) begin
                        if (hl_sqr.meta_behav == config_item::META_EOF && META_WIDTH != 0) begin
                            gen.meta[it] = meta.data;
                        end
                        eof[it]     = 1'b1;
                        gen.eof_pos[it] = index*BLOCK_SIZE + loop_end-1;
                        item_done();
                        state_packet = state_packet_space_new;
                    end
                end

                index++;
            end
        end

        if (src_rdy == 1) begin
            gen.src_rdy = 1;
            gen.sof     = sof;
            gen.eof     = eof;
        end
    endtask

    task body;
        if (rdy_probability > 100) begin
            rdy_probability = 100;
        end
        super.body();
    endtask
endclass

class sequence_rx_burst #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned BLOCK_SIZE,
    int unsigned ITEM_WIDTH,
    int unsigned META_WIDTH
) extends sequence_rx_base #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH);
    `ndk_object_param_utils(
        uvm_logic_vector_array_mfb::sequence_rx_burst#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH),
        $sformatf("uvm_logic_vector_array_mfb::sequence_rx_burst #(%0d,%0d,%0d,%0d,%0d)", REGIONS, REGION_SIZE,
                  BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)
    )

    rand int unsigned rdy_probability_min;
    rand int unsigned rdy_probability_max;

    constraint c_rdy_probability {
        rdy_probability_min != 0;
        rdy_probability_max != 0;

        rdy_probability_min <= rdy_probability_max;
        rdy_probability_min dist {
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*0 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*1] :/ 3,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*1 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*2] :/ 1,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*2 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*3] :/ 1,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*3 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*4] :/ 1,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*4 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*5] :/ 3,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*5 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*6] :/ 5,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*6 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*7] :/ 10,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*7 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*8] :/ 20,
             cfg.rdy_probability_max :/ 30
        };

        rdy_probability_max dist {
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*0 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*1] :/ 3,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*1 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*2] :/ 1,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*2 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*3] :/ 1,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*3 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*4] :/ 1,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*4 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*5] :/ 3,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*5 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*6] :/ 5,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*6 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*7] :/ 10,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*7 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*8] :/ 20,
             cfg.rdy_probability_max :/ 30
        };
    }

    rand int unsigned burst_size;
    constraint c_burst_size {
        burst_size inside { [10:100] };
    }


    typedef enum{SPACE, PACKET} fsm_t;
    fsm_t burst_state = SPACE;
    int unsigned size = 0;

    function new (string name = "sequence_rx_burst");
        super.new(name);
    endfunction

    /////////
    // CREATE uvm_intel_mac_seg::Sequence_item
    virtual task create_sequence_item();
        logic src_rdy;
        logic [REGIONS-1 : 0] sof;
        logic [REGIONS-1 : 0] eof;

        tr_init(gen);
        src_rdy = 0;
        sof     = '0;
        eof     = '0;

        if (size == 0) begin
            case (burst_state)
                SPACE : begin
                    size = $urandom_range(rdy_probability_min, rdy_probability_max)*burst_size;
                    burst_state = PACKET;
                end

                PACKET : begin
                    if (rdy_probability_min < 100) begin
                        size = $urandom_range(100 - rdy_probability_max, 100 - rdy_probability_min)*burst_size;
                        burst_state = SPACE;
                    end else begin
                        size = $urandom_range(rdy_probability_min, rdy_probability_max)*burst_size;
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
                        space_size   = cfg.space_size_min;
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
                        if (sof[it] == 1 ||
                                (eof[it] == 1'b1 && (REGION_SIZE*BLOCK_SIZE) >= (index*BLOCK_SIZE + data.data.size()))
                        ) begin
                            break;
                        end

                        sof[it]     = 1'b1;
                        gen.sof_pos[it] = index;
                        if (hl_sqr.meta_behav == config_item::META_SOF && META_WIDTH != 0) begin
                            gen.meta[it] = meta.data;
                        end
                        state_packet = state_packet_data;
                    end

                    if (state_packet == state_packet_data) begin
                        const int unsigned data_rest = (data.data.size() - data_index);
                        const int unsigned loop_end = BLOCK_SIZE < data_rest ? BLOCK_SIZE : data_rest;
                        src_rdy = 1;

                        for (int unsigned jt = index*BLOCK_SIZE; jt < (index*BLOCK_SIZE + loop_end); jt++) begin
                            gen.data[it][(jt+1)*ITEM_WIDTH-1 -: ITEM_WIDTH] = data.data[data_index];
                            data_index++;
                        end

                        // End of packet
                        if (data.data.size() <= data_index) begin
                            if (hl_sqr.meta_behav == config_item::META_EOF && META_WIDTH != 0) begin
                                gen.meta[it] = meta.data;
                            end
                            eof[it]     = 1'b1;
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

        if (src_rdy == 1) begin
            gen.src_rdy = 1;
            gen.sof     = sof;
            gen.eof     = eof;
        end
    endtask

    task body();
        burst_state = SPACE;
        size = 0;
        super.body();
    endtask
endclass


class sequence_rx_position #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned BLOCK_SIZE,
    int unsigned ITEM_WIDTH,
    int unsigned META_WIDTH
) extends sequence_rx_base #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH);
    `ndk_object_param_utils(
        uvm_logic_vector_array_mfb::sequence_rx_position#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH),
        $sformatf("uvm_logic_vector_array_mfb::sequence_rx_position #(%0d,%0d,%0d,%0d,%0d)", REGIONS, REGION_SIZE,
                  BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)
    )

    rand logic [REGION_SIZE-1:0] sof_pos;
    constraint sof_pos_c {sof_pos > 0;};

    rand int unsigned space_size_min;
    rand int unsigned space_size_max;
    constraint c_space_size {
        space_size_min <= space_size_max;
        space_size_min dist {
             cfg.space_size_min :/ 5,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*0 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*1] :/ 20,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*1 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*2] :/ 7,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*2 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*3] :/ 5,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*3 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*4] :/ 3,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*4 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*5] :/ 2,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*5 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*6] :/ 1,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*6 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*7] :/ 1,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*7 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*8] :/ 3,
             cfg.space_size_max :/ 5
        };

        space_size_max dist {
             cfg.space_size_min :/ 5,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*0 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*1] :/ 20,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*1 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*2] :/ 7,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*2 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*3] :/ 5,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*3 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*4] :/ 3,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*4 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*5] :/ 2,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*5 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*6] :/ 1,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*6 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*7] :/ 1,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*7 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*8] :/ 3,
             cfg.space_size_max :/ 5
        };
    }

    rand int unsigned rdy_probability;
    constraint c_rdy_probability {
        rdy_probability != 0;
        rdy_probability dist {
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*0 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*1] :/ 3,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*1 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*2] :/ 1,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*2 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*3] :/ 1,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*3 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*4] :/ 1,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*4 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*5] :/ 3,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*5 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*6] :/ 5,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*6 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*7] :/ 10,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*7 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*8] :/ 20,
             cfg.rdy_probability_max :/ 30
        };
    }



    function new (string name = "sequence_rx_simple");
        super.new(name);
    endfunction

    /////////
    // CREATE uvm_intel_mac_seg::Sequence_item
    virtual task create_sequence_item();
        logic src_rdy;
        logic [REGIONS-1 : 0] sof;
        logic [REGIONS-1 : 0] eof;

        tr_init(gen);
        src_rdy = 0;
        sof     = '0;
        eof     = '0;

        //randomization of rdy
        if ($urandom_range(0,100) > rdy_probability) begin
            return;
        end

        for (int unsigned it = 0; it < REGIONS; it++) begin
            int unsigned index = 0;
            while (index < REGION_SIZE) begin
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
                    if (sof_pos[index] == 1) begin //get next packet only if there is position for sof
                        try_get();
                    end
                end

                if (state_packet == state_packet_new) begin
                    // Check SOF and EOF position if we can insert packet into this region
                    if (sof[it] == 1 ||
                            (eof[it] == 1'b1 && (REGION_SIZE*BLOCK_SIZE) >= (index*BLOCK_SIZE + data.data.size()))
                    ) begin
                        break;
                    end

                    sof[it]     = 1'b1;
                    gen.sof_pos[it] = index;
                    if (hl_sqr.meta_behav ==  config_item::META_SOF && META_WIDTH != 0) begin
                        gen.meta[it] = meta.data;
                    end
                    state_packet = state_packet_data;
                end

                if (state_packet == state_packet_data) begin
                    const int unsigned data_rest = (data.data.size() - data_index);
                    const int unsigned loop_end   = BLOCK_SIZE < data_rest ? BLOCK_SIZE : data_rest;
                    src_rdy = 1;

                    for (int unsigned jt = index*BLOCK_SIZE; jt < (index*BLOCK_SIZE + loop_end); jt++) begin
                        gen.data[it][(jt+1)*ITEM_WIDTH-1 -: ITEM_WIDTH] = data.data[data_index];
                        data_index++;
                    end

                    // End of packet
                    if (data.data.size() <= data_index) begin
                        if (hl_sqr.meta_behav ==  config_item::META_EOF && META_WIDTH != 0) begin
                            gen.meta[it] = meta.data;
                        end
                        eof[it]     = 1'b1;
                        gen.eof_pos[it] = index*BLOCK_SIZE + loop_end-1;
                        item_done();
                        state_packet = state_packet_space_new;
                    end
                end

                index++;
            end
        end

        if (src_rdy == 1) begin
            gen.src_rdy = 1;
            gen.sof     = sof;
            gen.eof     = eof;
        end
    endtask
endclass


class sequence_rx_full_speed #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned BLOCK_SIZE,
    int unsigned ITEM_WIDTH,
    int unsigned META_WIDTH
) extends sequence_rx_base #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH);
    `ndk_object_param_utils(
        uvm_logic_vector_array_mfb::sequence_rx_full_speed#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH),
        $sformatf("uvm_logic_vector_array_mfb::sequence_rx_full_speed #(%0d,%0d,%0d,%0d,%0d)", REGIONS, REGION_SIZE,
                  BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)
    )

    function new (string name = "sequence_rx_full_speed");
        super.new(name);
    endfunction

    /////////
    // CREATE uvm_intel_mac_seg::Sequence_item
    virtual task create_sequence_item();
        int unsigned index = 0;
        logic src_rdy;
        logic [REGIONS-1 : 0] sof;
        logic [REGIONS-1 : 0] eof;

        tr_init(gen);
        src_rdy = 0;
        sof     = '0;
        eof     = '0;

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
                    if (sof[it] == 1 ||
                            (eof[it] == 1'b1 && (REGION_SIZE*BLOCK_SIZE) >= (index*BLOCK_SIZE + data.data.size()))
                    ) begin
                        break;
                    end

                    sof[it]     = 1'b1;
                    gen.sof_pos[it] = index;
                    if (hl_sqr.meta_behav ==  config_item::META_SOF && META_WIDTH != 0) begin
                        gen.meta[it] = meta.data;
                    end
                    state_packet = state_packet_data;
                end

                if (state_packet == state_packet_data) begin
                    const int unsigned data_rest = (data.data.size() - data_index);
                    const int unsigned loop_end   = BLOCK_SIZE < data_rest ? BLOCK_SIZE : data_rest;
                    src_rdy = 1;

                    for (int unsigned jt = index*BLOCK_SIZE; jt < (index*BLOCK_SIZE + loop_end); jt++) begin
                        gen.data[it][(jt+1)*ITEM_WIDTH-1 -: ITEM_WIDTH] = data.data[data_index];
                        data_index++;
                    end

                    // End of packet
                    if (data.data.size() <= data_index) begin
                        if (hl_sqr.meta_behav ==  config_item::META_EOF && META_WIDTH != 0) begin
                            gen.meta[it] = meta.data;
                        end
                        eof[it]     = 1'b1;
                        gen.eof_pos[it] = index*BLOCK_SIZE + loop_end-1;
                        item_done();
                        state_packet = state_packet_space_new;
                    end
                end
                index++;
            end
        end

        if (src_rdy == 1) begin
            gen.src_rdy = 1;
            gen.sof     = sof;
            gen.eof     = eof;
        end
    endtask
endclass

class sequence_rx_stop #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned BLOCK_SIZE,
    int unsigned ITEM_WIDTH,
    int unsigned META_WIDTH
) extends sequence_rx_base #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH);
    `ndk_object_param_utils(
        uvm_logic_vector_array_mfb::sequence_rx_stop#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH),
        $sformatf("uvm_logic_vector_array_mfb::sequence_rx_stop #(%0d,%0d,%0d,%0d,%0d)", REGIONS, REGION_SIZE,
                  BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)
    )

    function new (string name = "sequence_rx_stop");
        super.new(name);
        hl_transactions_min = 30;
        hl_transactions_max = 500;
    endfunction

    /////////
    // CREATE uvm_intel_mac_seg::Sequence_item
    virtual task create_sequence_item();
        int unsigned index = 0;
        tr_init(gen);

        if (hl_transactions != 0) begin
            hl_transactions--;
        end
    endtask
endclass
