//-- sequence.sv: Mfb sequence
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet>

//-- SPDX-License-Identifier: BSD-3-Clause

class sequence_burst_pcie_rx #(int unsigned REGIONS, int unsigned REGION_SIZE, int unsigned BLOCK_SIZE, int unsigned ITEM_WIDTH, int unsigned META_WIDTH) extends sequence_simple_rx_base #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH);
    `uvm_object_param_utils(uvm_logic_vector_array_mfb::sequence_burst_pcie_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))
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
                    assert(rand_burst_size.randomize());
                    size = rand_burst_size.m_value;
                    burst_state = PACKET;
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

                        if (index != 0 || (it != 0 && cfg.straddling == 0))
                            break;

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

class sequence_full_speed_pcie_rx #(int unsigned REGIONS, int unsigned REGION_SIZE, int unsigned BLOCK_SIZE, int unsigned ITEM_WIDTH, int unsigned META_WIDTH) extends sequence_simple_rx_base #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH);
    `uvm_object_param_utils(uvm_logic_vector_array_mfb::sequence_full_speed_pcie_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))

    function new (string name = "sequence_full_speed_pcie_rx");
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

                    if (index != 0 || (it != 0 && cfg.straddling == 0))
                        break;

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

// This is only a slight modification of the sequence_full_speed_rx class where no gaps inside frame are inserted.
// But there are abitrary long gaps getween frames.
class seqv_no_inframe_gap_rx #(int unsigned REGIONS, int unsigned REGION_SIZE, int unsigned BLOCK_SIZE, int unsigned ITEM_WIDTH, int unsigned META_WIDTH) extends sequence_simple_rx_base #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH);
    `uvm_object_param_utils(uvm_logic_vector_array_mfb::seqv_no_inframe_gap_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))

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
        int unsigned index = 0;
        gen.randomize();

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
                    try_get();
                end

                if (state_packet == state_packet_new) begin
                    // Check SOF and EOF position if we can insert packet into this region
                    if (gen.sof[it] == 1 || (gen.eof[it] == 1'b1 && (REGION_SIZE*BLOCK_SIZE) >= (index*BLOCK_SIZE + data.data.size()))) begin
                        break;
                    end

                    if (index != 0 || (it != 0 && cfg.straddling == 0))
                        break;

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

/////////////////////////////////////////////////////////////////////////
// SEQUENCE LIBRARY RX

class sequence_lib_pcie_rx #(int unsigned REGIONS, int unsigned REGION_SIZE, int unsigned BLOCK_SIZE, int unsigned ITEM_WIDTH, int unsigned META_WIDTH) extends uvm_common::sequence_library#(config_sequence, uvm_mfb::sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH));
  `uvm_object_param_utils(uvm_logic_vector_array_mfb::sequence_lib_pcie_rx#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))
  `uvm_sequence_library_utils(uvm_logic_vector_array_mfb::sequence_lib_pcie_rx#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))

  function new(string name = "sequence_lib_pcie_rx");
    super.new(name);
    init_sequence_library();
  endfunction

    // subclass can redefine and change run sequences
    // can be useful in specific tests
    virtual function void init_sequence(config_sequence param_cfg = null);
        super.init_sequence(param_cfg);
        this.add_sequence(uvm_logic_vector_array_mfb::sequence_full_speed_pcie_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::get_type());
        this.add_sequence(uvm_logic_vector_array_mfb::seqv_no_inframe_gap_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::get_type());
        this.add_sequence(uvm_logic_vector_array_mfb::sequence_stop_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::get_type());
        this.add_sequence(uvm_logic_vector_array_mfb::sequence_burst_pcie_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::get_type());
    endfunction
endclass

