//-- sequence.sv: Mfb sequence
//-- Copyright (C) 2026 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class sequence_rx #(
    int unsigned ITEMS,
    int unsigned ITEM_WIDTH
) extends uvm_common::sequence_base#(config_sequence, uvm_axi::sequence_item#(ITEMS, ITEM_WIDTH, 0));
    `uvm_object_param_utils(uvm_logic_vector_array_axi::sequence_rx#(ITEMS, ITEM_WIDTH))
    `uvm_declare_p_sequencer(uvm_axi::sequencer#(ITEMS, ITEM_WIDTH, 0))

    rand int unsigned space_size_min;
    rand int unsigned space_size_max;
    rand int unsigned rdy_probability;
    rand int unsigned transactions;

    uvm_logic_vector_array::sequencer #(ITEM_WIDTH) hl_sqr;

    constraint c_transactions {
        transactions inside { [10:500] };
    }

    constraint c_packet_space {
        space_size_min <= space_size_max;
        space_size_min dist {
            cfg.space_size_min :/ 5,
           `ndk_rand_dist_first(cfg.space_size_min, cfg.space_size_max, 8) :/ 20,
           `ndk_rand_dist      (cfg.space_size_min, cfg.space_size_max, 8, 1)  :/ 7,
           `ndk_rand_dist      (cfg.space_size_min, cfg.space_size_max, 8, 2)  :/ 5,
           `ndk_rand_dist      (cfg.space_size_min, cfg.space_size_max, 8, 3)  :/ 3,
           `ndk_rand_dist      (cfg.space_size_min, cfg.space_size_max, 8, 4)  :/ 2,
           `ndk_rand_dist      (cfg.space_size_min, cfg.space_size_max, 8, 5)  :/ 1,
           `ndk_rand_dist      (cfg.space_size_min, cfg.space_size_max, 8, 6)  :/ 1,
           `ndk_rand_dist_last (cfg.space_size_min, cfg.space_size_max, 8) :/ 3,
            cfg.space_size_max :/ 5
        };
        space_size_max dist {
            cfg.space_size_min :/ 5,
           `ndk_rand_dist_first(cfg.space_size_min, cfg.space_size_max, 8) :/ 20,
           `ndk_rand_dist      (cfg.space_size_min, cfg.space_size_max, 8, 1)  :/ 7,
           `ndk_rand_dist      (cfg.space_size_min, cfg.space_size_max, 8, 2)  :/ 5,
           `ndk_rand_dist      (cfg.space_size_min, cfg.space_size_max, 8, 3)  :/ 3,
           `ndk_rand_dist      (cfg.space_size_min, cfg.space_size_max, 8, 4)  :/ 2,
           `ndk_rand_dist      (cfg.space_size_min, cfg.space_size_max, 8, 5)  :/ 1,
           `ndk_rand_dist      (cfg.space_size_min, cfg.space_size_max, 8, 6)  :/ 1,
           `ndk_rand_dist_last (cfg.space_size_min, cfg.space_size_max, 8) :/ 3,
            cfg.space_size_max :/ 5
        };
    }

    constraint c_rdy_probability {
        rdy_probability dist {
           `ndk_rand_dist_first(cfg.rdy_probability_min, cfg.rdy_probability_max, 8) :/ 3,
           `ndk_rand_dist      (cfg.rdy_probability_min, cfg.rdy_probability_max, 8, 1)  :/ 1,
           `ndk_rand_dist      (cfg.rdy_probability_min, cfg.rdy_probability_max, 8, 2)  :/ 1,
           `ndk_rand_dist      (cfg.rdy_probability_min, cfg.rdy_probability_max, 8, 3)  :/ 1,
           `ndk_rand_dist      (cfg.rdy_probability_min, cfg.rdy_probability_max, 8, 4)  :/ 3,
           `ndk_rand_dist      (cfg.rdy_probability_min, cfg.rdy_probability_max, 8, 5)  :/ 5,
           `ndk_rand_dist      (cfg.rdy_probability_min, cfg.rdy_probability_max, 8, 6)  :/ 10,
           `ndk_rand_dist_last (cfg.rdy_probability_min, cfg.rdy_probability_max, 8) :/ 20,
            cfg.rdy_probability_max :/ 30
        };
    }


    protected int unsigned packet_space;

    function new(string name = "sequence_axi_converter");
        super.new(name);
    endfunction

    task send_empty_frame();
        start_item(req);
        assert(req.randomize() with {req.tvalid == 0;});
        finish_item(req);
    endtask

    task send_frame();
        start_item(req);
        finish_item(req);
    endtask

    task wait_to_accept();
        get_response(rsp);
        while(req.tvalid == 1 && rsp.tready == 0) begin
            send_frame();
            get_response(rsp);
        end
    endtask

    function void create_frame(inout uvm_axi::sequence_item#(ITEMS, ITEM_WIDTH, 0) tr,
                               inout int unsigned data_index,
                               input logic [ITEM_WIDTH-1:0] data[]
    );
        int unsigned it;

        tr.tkeep = '0;
        tr.tlast = 0;

        it = 0;
        while (it < ITEMS && data_index < data.size()) begin
            tr.tdata[it] = data[data_index];
            tr.tkeep[it] = 1;

            it++;
            data_index++;
        end

        if (data_index >= data.size()) begin
            tr.tlast = 1;
        end
    endfunction

    task body();
        uvm_logic_vector_array::sequence_item#(ITEM_WIDTH) data;
        int unsigned it;

        if(!uvm_config_db#(uvm_logic_vector_array::sequencer #(ITEM_WIDTH))::get(
            p_sequencer, "" , "hl_sqr", hl_sqr)
        ) begin
            `uvm_fatal(m_sequencer.get_full_name(), "\n\tsequence sequence_rx_simple cannot get hl_sqr");
        end
        req = uvm_axi::sequence_item#(ITEMS, ITEM_WIDTH, 0)::type_id::create("req", m_sequencer);

        // Send empty frame before
        // we have to work between two sends
        send_empty_frame();

        it = 0;
        while(it < transactions) begin
            int unsigned data_index;

            //////////////////////
            // Send empty frames befor packet
            std::randomize(packet_space) with {
                packet_space inside { [space_size_min : space_size_max] };
            };

            while (packet_space > 0) begin
                wait_to_accept();
                send_empty_frame();
                packet_space--;
            end

            //////////////////////
            // get high level transaction
            hl_sqr.try_next_item(data);

            while(data == null) begin
                wait_to_accept();
                send_empty_frame();
                hl_sqr.try_next_item(data);
            end

            data_index = 0;
            while(data_index < data.data.size()) begin

                assert(req.randomize() with {req.tvalid dist {
                            1'b0 :/ rdy_probability < 100 ? 100-rdy_probability : 0,
                            1'b1 :/ rdy_probability
                        };
                    }
                ) else begin
                    `uvm_fatal(m_sequencer.get_full_name(), "\n\tCannot randomize req");
                end

                // Generate valid DATA to AXI
                if (req.tvalid == 1) begin
                    create_frame(req, data_index, data.data);
                end

                wait_to_accept();
                send_frame();
            end

            hl_sqr.item_done();

            it++;
        end

        //Wait to accept last word
        wait_to_accept();

    endtask

endclass



