// sequence_one_frame.sv: Generates MFB transactions with a maximum of one frame per word
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class sequence_one_frame #(int unsigned MFB_REGIONS, int unsigned MFB_REGION_SIZE, int unsigned MFB_BLOCK_SIZE, int unsigned MFB_ITEM_WIDTH, int unsigned MFB_META_WIDTH) extends uvm_logic_vector_array_mfb::sequence_simple_rx #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH);
    `uvm_object_param_utils(test::sequence_one_frame #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH))

    function new (string name = "sequence_one_frame");
        super.new(name);
    endfunction

    virtual task create_sequence_item();
        int unsigned rdy;
        gen.randomize();

        // Randomization of READY
        assert(std::randomize(rdy) with { rdy dist {0 :/ (100 -rdy_probability), 1 :/ rdy_probability}; } );
        if (rdy == 0) begin
            gen.src_rdy = 0;
            return;
        end

        gen.src_rdy = 0;
        gen.sof     = '0;
        gen.eof     = '0;

        for (int unsigned region = 0; region < REGIONS; region++) begin
            for (int unsigned index = 0; index < REGION_SIZE; index++) begin
                if (state_packet == state_packet_space_new) begin
                    space_size = $urandom_range(space_size_min, space_size_max);;
                    state_packet = state_packet_space;
                end

                if (state_packet == state_packet_space) begin
                    if (space_size != 0) begin
                        space_size--;
                    end
                    else begin
                        state_packet = state_packet_none;
                    end
                end

                if (state_packet == state_packet_none) begin
                    try_get();
                end

                if (state_packet == state_packet_new) begin
                    // Check SOF and EOF position if we can insert packet into this region
                    if ($countones(gen.sof) > 0 || (gen.eof[region] == 1'b1 && (REGION_SIZE*BLOCK_SIZE) >= (index*BLOCK_SIZE + data.data.size()))) begin
                        break;
                    end

                    gen.sof[region]     = 1'b1;
                    gen.sof_pos[region] = index;
                    if (hl_sqr.meta_behav == uvm_logic_vector_array_mfb::config_item::META_SOF && META_WIDTH != 0) begin
                        gen.meta[region] = meta.data;
                    end
                    state_packet = state_packet_data;
                end

                if (state_packet == state_packet_data) begin
                    int unsigned loop_end  = BLOCK_SIZE < (data.data.size() - data_index) ? BLOCK_SIZE : (data.data.size() - data_index);
                    gen.src_rdy = 1;

                    for (int unsigned jt = index*BLOCK_SIZE; jt < (index*BLOCK_SIZE + loop_end); jt++) begin
                        gen.data[region][(jt+1)*ITEM_WIDTH-1 -: ITEM_WIDTH] = data.data[data_index];
                        data_index++;
                    end

                    // End of packet
                    if (data.data.size() <= data_index) begin
                        if (hl_sqr.meta_behav == uvm_logic_vector_array_mfb::config_item::META_EOF && META_WIDTH != 0) begin
                            gen.meta[region] = meta.data;
                        end
                        gen.eof[region]     = 1'b1;
                        gen.eof_pos[region] = index*BLOCK_SIZE + loop_end-1;
                        item_done();
                        state_packet = state_packet_space_new;
                    end
                end
            end
        end
    endtask

endclass

class sequence_lib_one_frame #(int unsigned MFB_REGIONS, int unsigned MFB_REGION_SIZE, int unsigned MFB_BLOCK_SIZE, int unsigned MFB_ITEM_WIDTH, int unsigned MFB_META_WIDTH) extends uvm_logic_vector_array_mfb::sequence_lib_rx #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH);
    `uvm_object_param_utils(test::sequence_lib_one_frame #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH))
    `uvm_sequence_library_utils(test::sequence_lib_one_frame #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH))

    function new(string name = "sequence_lib_one_frame");
        super.new(name);
        init_sequence_library();
    endfunction

    virtual function void init_sequence(uvm_logic_vector_array_mfb::config_sequence param_cfg = null);
        uvm_common::sequence_library::init_sequence(param_cfg);

        add_sequence(test::sequence_one_frame #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH)::get_type());
    endfunction

endclass
