//-- sequence.sv: AXI sequence
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


// This low level sequence define bus functionality
class sequence_simple_rx_base #(int unsigned DATA_WIDTH, int unsigned TUSER_WIDTH, int unsigned REGIONS, int unsigned BLOCK_SIZE, logic STRADDLING) extends uvm_common::sequence_base#(config_sequence, uvm_axi::sequence_item #(DATA_WIDTH, TUSER_WIDTH, REGIONS));
    `uvm_object_param_utils(uvm_logic_vector_array_axi::sequence_simple_rx_base#(DATA_WIDTH, TUSER_WIDTH, REGIONS, BLOCK_SIZE, STRADDLING))
    `uvm_declare_p_sequencer(uvm_axi::sequencer#(DATA_WIDTH, TUSER_WIDTH, REGIONS));

    localparam ITEM_WIDTH   = 32;
    localparam REGION_ITEMS = DATA_WIDTH/ITEM_WIDTH/REGIONS;
    int unsigned space_size = 0;
    int unsigned data_index;
    uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)         data;
    sequencer_rx #(ITEM_WIDTH)                                 hl_sqr;
    uvm_axi::sequence_item #(DATA_WIDTH, TUSER_WIDTH, REGIONS) gen;
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
        req.tvalid = 0;
        finish_item(req);
    endtask

    function void item_done();
        hl_sqr.m_data.item_done();
        data = null;
    endfunction

    task try_get();
        if (data == null && hl_transactions != 0) begin
            hl_sqr.m_data.try_next_item(data);
            data_index = 0;
            if (data != null) begin
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
            gen.tvalid = 0;
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
            if (rsp.tvalid == 1'b1 && rsp.tready == 1'b0) begin
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
        if(!uvm_config_db#(sequencer_rx #(ITEM_WIDTH))::get(p_sequencer, "" , "hl_sqr", hl_sqr)) begin
            `uvm_fatal(p_sequencer.get_full_name(), "\n\tsequence sequence_simple_rx cannot get hl_sqr");
        end

        data = null;
        space_size = 0;
        state_packet = state_packet_space_new;

        req = uvm_axi::sequence_item #(DATA_WIDTH, TUSER_WIDTH, REGIONS)::type_id::create("req");
        gen = uvm_axi::sequence_item #(DATA_WIDTH, TUSER_WIDTH, REGIONS)::type_id::create("gen");

        //send empty frame to get first response
        send_empty_frame();
        //when reset on start then wait
        req.tvalid = 0;
        gen.tvalid = 0;
        state = state_next;

        while (hl_transactions > 0 || data != null || state == state_last || gen.tvalid == 1) begin
            send_frame();
        end
        //Get last response
        get_response(rsp);
    endtask
endclass

class sequence_simple_rx #(int unsigned DATA_WIDTH, int unsigned TUSER_WIDTH, int unsigned REGIONS, int unsigned BLOCK_SIZE, logic STRADDLING) extends sequence_simple_rx_base #(DATA_WIDTH, TUSER_WIDTH, REGIONS, BLOCK_SIZE, STRADDLING);
    `uvm_object_param_utils(uvm_logic_vector_array_axi::sequence_simple_rx #(DATA_WIDTH, TUSER_WIDTH, REGIONS, BLOCK_SIZE, STRADDLING))
    uvm_common::rand_length   rdy_length;
    uvm_common::rand_rdy      rdy_rdy;
    logic[3 : 0] is_sop              = '0;
    logic[3 : 0] is_sop_ptr[REGIONS] = '{default: '0};
    logic[3 : 0] is_eop              = '0;
    logic[3 : 0] is_eop_ptr[REGIONS] = '{default: '0};
    int sop_cnt = 0;
    int eop_cnt = 0;

    function new (string name = "sequence_simple_rx");
        super.new(name);
        rdy_length = uvm_common::rand_length_rand::new();
        rdy_rdy    = uvm_common::rand_rdy_rand::new();
    endfunction

    function logic[1 : 0] sof_pos_count (int index);
        logic[1 : 0] ret = 0;
        if (TUSER_WIDTH == 183) begin
            case (index)
                0 : ret = 2'b00;
                1 : ret = 2'b10;
            endcase
        end else begin
            case (index)
                0 : ret = 2'b00;
                1 : ret = 2'b01;
                2 : ret = 2'b10;
                3 : ret = 2'b11;
            endcase
        end
        return ret;
    endfunction

    virtual task create_sequence_item();
        gen.randomize();

        //randomization of rdy
        void'(rdy_rdy.randomize());
        if (rdy_rdy.m_value == 0) begin
            gen.tvalid = 0;
            return;
        end

        gen.tvalid = 0;
        // SOF
        is_sop     = '0;
        gen.tuser  = '0;
        // Requester side
        if (TUSER_WIDTH == 161) begin
            gen.tuser[67 : 64] = '0;
            gen.tuser[79 : 76] = '0;
            // TODO
            gen.tuser[63 : 0]  = '0;
        end else if (TUSER_WIDTH == 75) begin
            gen.tuser[33 : 32] = '0;
            gen.tuser[34]      = 1'b0;
            gen.tuser[38]      = 1'b0;
            // TODO
            gen.tuser[31 : 0]  = '0;
        // Completition side
        end else if(TUSER_WIDTH == 88 || TUSER_WIDTH == 85) begin
            gen.tuser[40]      = 1'b0;
            // TODO
            gen.tuser[3 : 0]   = '1;
            gen.tuser[7 : 4]   = '1;
            gen.tuser[39 : 8]  = '0;
        end else if(TUSER_WIDTH == 183) begin
            gen.tuser[81 : 80] = '0;
            gen.tuser[87 : 86] = '0;
            // TODO
            gen.tuser[7 : 0]   = '1;
            gen.tuser[15 : 8]  = '1;
            gen.tuser[79 : 16] = '0;
        end
        // EOF
        is_eop = '0;
        sop_cnt = 0;
        eop_cnt = 0;
        gen.tlast = 1'b0;
        gen.tkeep = '1;

        for (int unsigned it = 0; it < REGIONS; it++) begin
            int unsigned index = 0;
            while (index < REGION_ITEMS) begin
                if (state_packet == state_packet_space_new) begin
                    void'(rdy_length.randomize());
                    space_size   = rdy_length.m_value;
                    state_packet = state_packet_space;
                    space_size   = 0;
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
                    if (is_sop[sop_cnt] == 1'b1 || (is_eop[eop_cnt] == 1'b1 && REGION_ITEMS > (index + data.data.size()))) begin
                        break;
                    end

                    if (index != 0 || (it != 0 && STRADDLING == 0))
                        break;

                    is_sop[sop_cnt]     = 1'b1;
                    is_sop_ptr[sop_cnt] = sof_pos_count(it);

                    if(TUSER_WIDTH == 88 || TUSER_WIDTH == 85)
                        gen.tuser[40]   = 1'b1;

                    sop_cnt++;
                    state_packet = state_packet_data;
                end

                if (state_packet == state_packet_data) begin
                    int unsigned loop_end   = REGION_ITEMS < (data.data.size() - data_index) ? REGION_ITEMS : (data.data.size() - data_index);
                    gen.tvalid = 1;

                    gen.tdata[it][(index+1)*ITEM_WIDTH-1 -: ITEM_WIDTH] = data.data[data_index];
                    data_index++;

                    // End of packet
                    if (data.data.size() <= data_index) begin
                        is_eop[eop_cnt]     = 1'b1;
                        is_eop_ptr[eop_cnt] = it*BLOCK_SIZE + index;
                        gen.tlast           = 1'b1;
                        gen.tkeep           = '0;
                        for (int unsigned jt = 0; jt < (it*BLOCK_SIZE + index+1); jt++) begin
                            gen.tkeep[jt] = 1'b1;
                        end
                        eop_cnt++;
                        item_done();
                        state_packet = state_packet_space_new;
                    end
                end

                index++;
            end
        end

        // Requester side
        if (TUSER_WIDTH == 161) begin
            // SOF fill
            gen.tuser[67 : 64] = is_sop;
            // EOF fill
            gen.tuser[79 : 76] = is_eop;
        end else if (TUSER_WIDTH == 75) begin
            // SOF fill
            gen.tuser[33 : 32] = is_sop;
        // Completition side
        end else if(TUSER_WIDTH == 183) begin
            // SOF fill
            gen.tuser[81 : 80] = is_sop;
            // EOF fill
            gen.tuser[87 : 86] = is_eop;
        end

        for (int unsigned it = 0; it < REGIONS; it++) begin
            if (TUSER_WIDTH == 161) begin
                if (is_sop[it]) begin
                    gen.tuser[(it*2 + 69) -: 2] = is_sop_ptr[it];
                end
                if (is_eop[it]) begin
                    gen.tuser[(it*4 + 83) -: 4] = is_eop_ptr[it];
                end
            end else if (TUSER_WIDTH == 75) begin
                if (is_eop[it]) begin
                    gen.tuser[(it*4 + 37) -: 3] = is_eop_ptr[it];
                end
                // EOF fill
                gen.tuser[((it*4) + 34)] = is_eop[it];
            end else if(TUSER_WIDTH == 183) begin
                if (is_sop[it]) begin
                    gen.tuser[(it*2 + 83) -: 2] = is_sop_ptr[it];
                end
                if (is_eop[it]) begin
                    gen.tuser[(it*4 + 91) -: 4] = is_eop_ptr[it];
                end
            end
        end
        if (|is_eop) begin
            gen.tlast = 1'b1;
        end

    endtask

    task body;
        rdy_length.bound_set(cfg.space_size_min, cfg.space_size_max);
        rdy_rdy.bound_set(cfg.rdy_probability_min, cfg.rdy_probability_max);

        super.body();
    endtask
endclass


class sequence_full_speed_rx #(int unsigned DATA_WIDTH, int unsigned TUSER_WIDTH, int unsigned REGIONS, int unsigned BLOCK_SIZE, logic STRADDLING) extends sequence_simple_rx_base #(DATA_WIDTH, TUSER_WIDTH, REGIONS, BLOCK_SIZE, STRADDLING);
    `uvm_object_param_utils(uvm_logic_vector_array_axi::sequence_full_speed_rx #(DATA_WIDTH, TUSER_WIDTH, REGIONS, BLOCK_SIZE, STRADDLING))
    uvm_common::rand_length   rdy_length;
    uvm_common::rand_rdy      rdy_rdy;
    logic[3 : 0] is_sop              = '0;
    logic[3 : 0] is_sop_ptr[REGIONS] = '{default: '0};
    logic[3 : 0] is_eop              = '0;
    logic[3 : 0] is_eop_ptr[REGIONS] = '{default: '0};
    int sop_cnt = 0;
    int eop_cnt = 0;

    function new (string name = "sequence_full_speed_rx");
        super.new(name);
        rdy_length = uvm_common::rand_length_rand::new();
        rdy_rdy    = uvm_common::rand_rdy_rand::new();
    endfunction

    function logic[1 : 0] sof_pos_count (int index);
        logic[1 : 0] ret = 0;
        if (TUSER_WIDTH == 183) begin
            case (index)
                0 : ret = 2'b00;
                1 : ret = 2'b10;
            endcase
        end else begin
            case (index)
                0 : ret = 2'b00;
                1 : ret = 2'b01;
                2 : ret = 2'b10;
                3 : ret = 2'b11;
            endcase
        end
        return ret;
    endfunction

    virtual task create_sequence_item();
        gen.randomize();

        //randomization of rdy
        void'(rdy_rdy.randomize());
        if (rdy_rdy.m_value == 0) begin
            gen.tvalid = 0;
            return;
        end

        gen.tvalid = 0;
        // SOF
        is_sop     = '0;
        gen.tuser  = '0;
        // Requester side
        if (TUSER_WIDTH == 161) begin
            gen.tuser[67 : 64] = '0;
            gen.tuser[79 : 76] = '0;
            // TODO
            gen.tuser[63 : 0]  = '0;
        end else if (TUSER_WIDTH == 75) begin
            gen.tuser[33 : 32] = '0;
            gen.tuser[34]      = 1'b0;
            gen.tuser[38]      = 1'b0;
            // TODO
            gen.tuser[31 : 0]  = '0;
        // Completition side
        end else if(TUSER_WIDTH == 88 || TUSER_WIDTH == 85) begin
            gen.tuser[40]      = 1'b0;
            // TODO
            gen.tuser[3 : 0]   = '1;
            gen.tuser[7 : 4]   = '1;
            gen.tuser[39 : 8]  = '0;
        end else if(TUSER_WIDTH == 183) begin
            gen.tuser[81 : 80] = '0;
            gen.tuser[87 : 86] = '0;
            // TODO
            gen.tuser[7 : 0]   = '1;
            gen.tuser[15 : 8]  = '1;
            gen.tuser[79 : 16] = '0;
        end
        // EOF
        is_eop    = '0;
        sop_cnt   = 0;
        eop_cnt   = 0;
        gen.tlast = 1'b0;
        gen.tkeep = '1;

        for (int unsigned it = 0; it < REGIONS; it++) begin
            int unsigned index = 0;
            while (index < REGION_ITEMS) begin
                if (state_packet == state_packet_space_new) begin
                    state_packet = state_packet_space;
                    space_size   = 0;
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
                    if (is_sop[sop_cnt] == 1'b1 || (is_eop[eop_cnt] == 1'b1 && REGION_ITEMS > (index + data.data.size()))) begin
                        break;
                    end

                    if (index != 0 || (it != 0 && STRADDLING == 0))
                        break;

                    is_sop[sop_cnt]     = 1'b1;
                    is_sop_ptr[sop_cnt] = sof_pos_count(it);

                    if(TUSER_WIDTH == 88 || TUSER_WIDTH == 85)
                        gen.tuser[40]   = 1'b1;

                    sop_cnt++;
                    state_packet = state_packet_data;
                end

                if (state_packet == state_packet_data) begin
                    int unsigned loop_end   = REGION_ITEMS < (data.data.size() - data_index) ? REGION_ITEMS : (data.data.size() - data_index);
                    gen.tvalid = 1;

                    gen.tdata[it][(index+1)*ITEM_WIDTH-1 -: ITEM_WIDTH] = data.data[data_index];
                    data_index++;

                    // End of packet
                    if (data.data.size() <= data_index) begin
                        is_eop[eop_cnt]     = 1'b1;
                        is_eop_ptr[eop_cnt] = it*BLOCK_SIZE + index;
                        gen.tkeep           = '0;
                        gen.tlast           = 1'b1;
                        for (int unsigned jt = 0; jt < (it*BLOCK_SIZE + index+1); jt++) begin
                            gen.tkeep[jt] = 1'b1;
                        end
                        eop_cnt++;
                        item_done();
                        state_packet = state_packet_space_new;
                    end
                end

                index++;
            end
        end

        // Requester side
        if (TUSER_WIDTH == 161) begin
            // SOF fill
            gen.tuser[67 : 64] = is_sop;
            // EOF fill
            gen.tuser[79 : 76] = is_eop;
        end else if (TUSER_WIDTH == 75) begin
            // SOF fill
            gen.tuser[33 : 32] = is_sop;
        // Completition side
        end else if(TUSER_WIDTH == 183) begin
            // SOF fill
            gen.tuser[81 : 80] = is_sop;
            // EOF fill
            gen.tuser[87 : 86] = is_eop;
        end

        for (int unsigned it = 0; it < REGIONS; it++) begin
            if (TUSER_WIDTH == 161) begin
                if (is_sop[it]) begin
                    gen.tuser[(it*2 + 69) -: 2] = is_sop_ptr[it];
                end
                if (is_eop[it]) begin
                    gen.tuser[(it*4 + 83) -: 4] = is_eop_ptr[it];
                end
            end else if (TUSER_WIDTH == 75) begin
                if (is_eop[it]) begin
                    gen.tuser[(it*4 + 37) -: 3] = is_eop_ptr[it];
                end
                // EOF fill
                gen.tuser[((it*4) + 34)] = is_eop[it];
            end else if(TUSER_WIDTH == 183) begin
                if (is_sop[it]) begin
                    gen.tuser[(it*2 + 83) -: 2] = is_sop_ptr[it];
                end
                if (is_eop[it]) begin
                    gen.tuser[(it*4 + 91) -: 4] = is_eop_ptr[it];
                end
            end
        end
        if (|is_eop) begin
            gen.tlast = 1'b1;
        end
    endtask
endclass

class sequence_stop_rx #(int unsigned DATA_WIDTH, int unsigned TUSER_WIDTH, int unsigned REGIONS, int unsigned BLOCK_SIZE, logic STRADDLING) extends sequence_simple_rx_base #(DATA_WIDTH, TUSER_WIDTH, REGIONS, BLOCK_SIZE, STRADDLING);
    `uvm_object_param_utils(uvm_logic_vector_array_axi::sequence_stop_rx #(DATA_WIDTH, TUSER_WIDTH, REGIONS, BLOCK_SIZE, STRADDLING))

    constraint c_hl_transations_stop {
        hl_transactions dist {[hl_transactions_min:hl_transactions_min + 100] :/ 50, [hl_transactions_max-100:hl_transactions_max] :/ 50, [hl_transactions_min:hl_transactions_max] :/100};
    }

    function new (string name = "sequence_stop_rx");
        super.new(name);
        hl_transactions_min = 10;
        hl_transactions_max = 1000;
    endfunction

    virtual task create_sequence_item();
        int unsigned index = 0;
        gen.randomize();

        gen.tvalid = 0;
        gen.tuser  = '0;

        // Requester side
        if (TUSER_WIDTH == 161) begin
            gen.tuser[67 : 64] = '0;
            gen.tuser[79 : 76] = '0;
        end else if (TUSER_WIDTH == 75) begin
            gen.tuser[33 : 32] = '0;
            gen.tuser[34]      = 1'b0;
            gen.tuser[38]      = 1'b0;
        // Completition side
        end else if(TUSER_WIDTH == 88 || TUSER_WIDTH == 85) begin
            gen.tuser[40]      = 1'b0;
            gen.tuser[3 : 0]   = '1;
            gen.tuser[7 : 4]   = '1;
            gen.tuser[39 : 8]  = '0;
            gen.tlast          = 1'b0;
        end else if(TUSER_WIDTH == 183) begin
            gen.tuser[7 : 0]   = '1;
            gen.tuser[15 : 8]  = '1;
            gen.tuser[79 : 16] = '0;
            gen.tuser[81 : 80] = '0;
            gen.tuser[87 : 86] = '0;
        end

        if (hl_transactions != 0) begin
            hl_transactions--;
        end
    endtask
endclass

// /////////////////////////////////////////////////////////////////////////
// // SEQUENCE LIBRARY RX

class sequence_lib_rx #(int unsigned DATA_WIDTH, int unsigned TUSER_WIDTH, int unsigned REGIONS, int unsigned BLOCK_SIZE, logic STRADDLING) extends uvm_common::sequence_library#(config_sequence, uvm_axi::sequence_item #(DATA_WIDTH, TUSER_WIDTH, REGIONS));
  `uvm_object_param_utils(uvm_logic_vector_array_axi::sequence_lib_rx#(DATA_WIDTH, TUSER_WIDTH, REGIONS, BLOCK_SIZE, STRADDLING))
  `uvm_sequence_library_utils(uvm_logic_vector_array_axi::sequence_lib_rx#(DATA_WIDTH, TUSER_WIDTH, REGIONS, BLOCK_SIZE, STRADDLING))

  function new(string name = "sequence_lib_rx");
    super.new(name);
    init_sequence_library();
  endfunction

    // subclass can redefine and change run sequences
    // can be useful in specific tests
    virtual function void init_sequence(config_sequence param_cfg = null);
        super.init_sequence(param_cfg);
        this.add_sequence(uvm_logic_vector_array_axi::sequence_simple_rx #(DATA_WIDTH, TUSER_WIDTH, REGIONS, BLOCK_SIZE, STRADDLING)::get_type());
        this.add_sequence(uvm_logic_vector_array_axi::sequence_full_speed_rx #(DATA_WIDTH, TUSER_WIDTH, REGIONS, BLOCK_SIZE, STRADDLING)::get_type());
        this.add_sequence(uvm_logic_vector_array_axi::sequence_stop_rx #(DATA_WIDTH, TUSER_WIDTH, REGIONS, BLOCK_SIZE, STRADDLING)::get_type());
    endfunction
endclass
